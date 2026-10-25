import Submission.Obl.k4_matching_cofinal_palette_selection.GoodSet
import Submission.Obl.k4_matching_cofinal_palette_selection.Cofinal
import Submission.Obl.k4_matching_cofinal_palette_selection.Estimates

namespace Submission.Obl.k4_matching_cofinal_palette_selection

def Selection (J : ℕ) (d : ℝ) (β : ℕ → ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ δ : ℝ, 0 < δ → ∃ Q : ℕ,
    ∀ q : ℕ, Q ≤ q → 1 ≤ q → ∀ (A : Finset ℕ) (m z : ℕ → ℕ) (u : ℕ → ℝ),
      Admissible J β (radius J β) (accuracy (radius J β)) q A m z γ →
      Cofinal (RecordData J d β (radius J β) (accuracy (radius J β)) q u) →
      ∃ G : Finset ℕ, G ⊆ A ∧ ((A \ G).card : ℝ) / (q : ℝ) ≤ δ ∧
        Cofinal (fun ε N => GoodRecordData J d β (radius J β) (accuracy (radius J β))
          q u ε N m z G (δ / (4 * ((J : ℝ) + 1) * (q : ℝ))))


/-- Cofinal homogeneous records have a fixed palette-good subset. -/
theorem selection (hpal : PaletteEstimate) (J : ℕ) (d : ℝ) (β : ℕ → ℝ) :
    Selection J d β := by
  intro γ hγ δ hδ
  obtain ⟨Q, hQ⟩ := bad_count_arith J δ hδ
  refine ⟨Q, ?_⟩
  intro q hQq hq A m z u hadm hco
  obtain ⟨N₀, hN₀, hcount⟩ := hQ q hQq hq
  apply cofinal_good_subset_of_large_records A hco N₀ hN₀
  intro ε N hN hr
  rcases hr with ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, hrec⟩
  obtain ⟨G, hGA, hcard, hgood⟩ := exists_good_set hpal hq hadm
    (by linarith : 1 ≤ N) hδ (hcount N hN) hrec
  exact ⟨G, hGA, hcard, n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, hrec, hgood⟩

end Submission.Obl.k4_matching_cofinal_palette_selection
