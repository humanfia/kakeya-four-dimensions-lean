-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.ContactChoices.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.ContactGridCover

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set

/-- Choose the two curve witnesses and contact time of every cell, with the
curve labels taking values in the actual finite color classes. -/
theorem choose_contactCell_witnesses {n : ℕ} (A B : Finset (Fin n))
    (hA : A.Nonempty) (hB : B.Nonempty) (g : Fin n → ℝ → ℝ) (f₀ : ℝ → ℝ)
    {δ lower s ℓ w l u : ℝ} (S : Finset (ℤ × ℤ × ℤ))
    (hS : ∀ t ∈ S, ContactCellWitness A B g f₀ δ lower s ℓ w l u t) :
    ∃ (red : ℤ × ℤ × ℤ → {i : Fin n // i ∈ A})
      (blue : ℤ × ℤ × ℤ → {j : Fin n // j ∈ B}) (tag : ℤ × ℤ × ℤ → ℝ),
      ∀ t ∈ S, tag t ∈ Icc l u ∧ |tag t - (w + t.1 * ℓ)| ≤ ℓ ∧
        NearContact (2 * δ) s (g (red t)) (g (blue t)) (tag t) ∧
        lower ≤ |deriv (g (red t)) (tag t) - deriv (g (blue t)) (tag t)| ∧
        JetCell (g (red t)) f₀ δ s ℓ w 42 t ∧
        JetCell (g (blue t)) f₀ δ s ℓ w 42 t := by
  classical
  obtain ⟨i₀, hi₀⟩ := hA
  obtain ⟨j₀, hj₀⟩ := hB
  have hchoice : ∀ t : ℤ × ℤ × ℤ,
      ∃ (a : {i : Fin n // i ∈ A}) (b : {j : Fin n // j ∈ B}) (x : ℝ),
        t ∈ S → x ∈ Icc l u ∧ |x - (w + t.1 * ℓ)| ≤ ℓ ∧
          NearContact (2 * δ) s (g a) (g b) x ∧
          lower ≤ |deriv (g a) x - deriv (g b) x| ∧
          JetCell (g a) f₀ δ s ℓ w 42 t ∧ JetCell (g b) f₀ δ s ℓ w 42 t := by
    intro t
    by_cases ht : t ∈ S
    · obtain ⟨i, hi, j, hj, x, hx, hnear, hc, hlo, hci, hcj⟩ := hS t ht
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩, x, fun _ => ⟨hx, hnear, hc, hlo, hci, hcj⟩⟩
    · exact ⟨⟨i₀, hi₀⟩, ⟨j₀, hj₀⟩, 0, fun h => (ht h).elim⟩
  choose red blue tag htag using hchoice
  exact ⟨red, blue, tag, htag⟩

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
