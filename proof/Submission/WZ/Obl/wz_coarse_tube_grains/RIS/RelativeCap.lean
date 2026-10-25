-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RelativeCap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RelativeIncidence

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

/-- Every angular-cap estimate passes through a relative-incidence
refinement, with the reciprocal of the retained pointwise fraction. -/
theorem angular_cap_bound_of_relative_incidence {n : ℕ}
    (v : Fin n → Space) {Y Z : Fin n → Set Space} {b q θ : ℝ}
    (hθ : 0 < θ) (hq : 0 ≤ q) (hZY : ∀ i, Z i ⊆ Y i)
    (hrelative : ∀ p ∈ ⋃ i, Z i, θ * incidence Y p ≤ incidence Z p)
    (hcap : ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤ q * incidence Y p) :
    ∀ p u, ‖u‖ = 1 →
      ({i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤ (q / θ) * incidence Z p := by
  intro p u hu
  by_cases hp : p ∈ ⋃ i, Z i
  · have hmono : ({i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) ≤
        ({i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b}.ncard : ℝ) := by
      exact_mod_cast Set.ncard_mono (show {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b} ⊆
        {i | p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b} from fun i hi => ⟨hZY i hi.1, hi.2⟩)
    have hrel : incidence Y p ≤ incidence Z p / θ := by
      apply (le_div_iff₀ hθ).mpr
      simpa only [mul_comm] using hrelative p hp
    exact (hmono.trans (hcap p u hu)).trans (by
      convert mul_le_mul_of_nonneg_left hrel hq using 1 <;> ring)
  · have hzero : {i | p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b} = ∅ := by
      ext i
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun hi => hp (mem_iUnion.mpr ⟨i, hi.1⟩)
    rw [hzero, ncard_empty, Nat.cast_zero, incidence_eq_zero_of_notMem Z hp, mul_zero]

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
