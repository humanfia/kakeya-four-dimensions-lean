-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CappedConcentration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CappedConcentration.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AmbientRefinement
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedState

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

noncomputable section

/-- Impose the all-radius density cap before the concentration reduction.
The new ambient family retains a prescribed small power of the old mass,
so a subsequent state can be lifted back to the original family. -/
theorem gain_terminal_or_capped_concentration {σ ω ζ ξ t : ℝ}
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    (hζ : 0 < ζ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ht : 0 < t) :
    ∃ (b κ θ d₀ : ℝ) (p : ℕ),
      0 < b ∧ b ≤ ξ / 384 ∧ 0 < κ ∧ 0 < θ ∧ θ ≤ ξ / 16 ∧
      0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ 0 < p ∧
      ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ θ →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V),
      A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
      ∀ ρ c, J ω ζ δ h ρ c n x v Y 2 →
      Gain σ ω κ (min (t / 4) (b * ω / 2)) δ n Y ∨
        J ω ζ δ (2 * ξ) ρ c n x v Y 3 ∨
        ∃ Y' : Fin n → Set V,
          (∀ i, Y' i ⊆ Y i) ∧
          O (δ ^ (ξ / 8)) * ∑ i, μ (Y i) ≤ ∑ i, μ (Y' i) ∧
          A δ (ξ / 4) (δ ^ (-(ξ / 4))) (δ ^ (-(ξ / 4))) n x v Y' ∧
          (∀ q ∈ ⋃ i, Y' i, ∀ r : ℝ, 0 < r → r ≤ 1 →
            μ ((⋃ i, Y' i) ∩ ball q r) ≤ O (δ ^ (-t) * (δ / r) ^ (ω + σ) * r ^ 3)) ∧
          Nonempty (ConcentratedGrainData ω ζ δ ξ b ρ c p n x v Y') := by
  obtain ⟨b, κ₁, θ₁, d₁, p, hb, hbξ, hκ₁, hθ₁, hθ₁ξ, hd₁, hd₁small, hp, Hreduce⟩ :=
    gain_terminal_or_concentrated_grains hσ hσhalf hω hE hζ hξ hξ1
  obtain ⟨u, κ₀, θ₀, d₂, hu, hut, hκ₀, hθ₀, hθ₀u, hd₂, hd₂small, Hcap⟩ :=
    gain_or_grain_density_cap hσ hσhalf hω hE t ht
  obtain ⟨d₃, hd₃, Hhalf⟩ := exists_rpow_cutoff hu (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨d₄, hd₄, Hquarter⟩ := exists_rpow_cutoff
    (by positivity : 0 < θ₁ / 4) (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨b, min κ₀ κ₁, min θ₀ (θ₁ / 4), min d₁ (min d₂ (min d₃ d₄)), p,
    hb, hbξ, lt_min hκ₀ hκ₁, lt_min hθ₀ (by positivity),
    (min_le_right _ _).trans (by linarith),
    lt_min hd₁ (lt_min hd₂ (lt_min hd₃ hd₄)), (min_le_left _ _).trans hd₁small, hp, ?_⟩
  intro δ h hδ hδd hh hhθ n x v Y hA ρ c hJ
  have hd := hδd
  simp only [le_min_iff] at hd
  obtain ⟨hδd₁, hδd₂, hδd₃, hδd₄⟩ := hd
  have hδ1 : δ ≤ 1 := hδd₁.trans (hd₁small.trans (by norm_num))
  have hhθ₀ := hhθ.trans (min_le_left _ _)
  have hhθ₁ := hhθ.trans (min_le_right _ _)
  have hκ : 0 ≤ min κ₀ κ₁ := (lt_min hκ₀ hκ₁).le
  obtain ⟨S, Z, N, y, w, f, a, g, hC, hρ, hg, hB, hG, hstop⟩ := hJ
  obtain ⟨L, z, e, Hg, γ, m, hG⟩ := hG
  rcases Hcap δ h hδ hδd₂ hh hhθ₀ n N L x v Y Z S y w f ρ a c 0 g z e Hg γ m
      hA hC hG with hgain | hcut
  · exact Or.inl (gain_bound_mono hδ hδ1 hκ (min_le_left _ _) (min_le_left _ _) hgain)
  obtain ⟨Γ, hΓ, hloss, hcap⟩ := hcut
  have hbudget : O (δ ^ (θ₁ / 2)) ≤ O (1 / 4 : ℝ) * O (δ ^ h) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ δ ^ (θ₁ / 4 + h) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ (θ₁ / 4) * δ ^ h := Real.rpow_add hδ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Hquarter δ hδ hδd₄) (by positivity)
  have hloss' : (∑ k, μ (Hg k \ Γ)) ≤ (1 / 2 : ENNReal) * ∑ k, μ (Hg k) := by
    apply hloss.trans
    apply mul_le_mul' _ le_rfl
    simpa [O, ENNReal.ofReal_div_of_pos] using ENNReal.ofReal_le_ofReal (Hhalf δ hδ hδd₃)
  obtain ⟨hA', hret, hJ'⟩ := stage_inside_common_cut (h' := θ₁ / 2) (h'' := θ₁)
    hδ hδ1 (by linarith) (by linarith) hbudget (by linarith)
    hA hC hρ hg hB hG hstop hΓ hloss'
  let Y' := fun i => Y i ∩ Γ
  have hsub : ∀ i, Y' i ⊆ Y i := fun _ => inter_subset_left
  have hJU : J ω ζ δ θ₁ ρ c n x v Y' 2 :=
    stage_mono hδ hδ1 (by linarith) hJ'
  rcases Hreduce δ θ₁ hδ hδd₁ hθ₁.le le_rfl n x v Y' hA' ρ c hJU with hgain | hrest
  · left
    exact (gain_bound_mono hδ hδ1 hκ (min_le_right _ _) (min_le_right _ _) hgain).trans
      (measure_mono (iUnion_mono hsub))
  rcases hrest with hterminal | hD
  · exact Or.inr (Or.inl (stage_mono hδ hδ1 (by linarith)
      (stage_of_ambient_refinement hδ hδ1 (by positivity) hsub hret hterminal)))
  right; right
  refine ⟨Y', hsub, ?_, admissible_mono hδ hδ1 hθ₁ξ hA', ?_, hD⟩
  · exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))) le_rfl).trans hret
  · intro q hq r hr hr1
    have hqΓ : q ∈ Γ := by obtain ⟨i, hqi⟩ := mem_iUnion.mp hq; exact hqi.2
    exact (measure_mono (inter_subset_inter_left _ (iUnion_mono hsub))).trans (hcap q hqΓ r hr hr1)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
