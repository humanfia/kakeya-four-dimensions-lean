-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_kaufman_projection_count.WeightedSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_kaufman_projection_count.Basic

/- Adapted from this tree’s o103 branch x0272, commit f2e1c96. -/

namespace WangZahlLot.Obl.wz_kaufman_projection_count

open scoped BigOperators

/-- Some positive-weight term has no larger energy-to-weight ratio than
the ratio of the two totals. This form avoids dividing by zero. -/
theorem exists_weighted_ratio {I : Type*} (S : Finset I) (E w : I → ℝ)
    (hE : ∀ i ∈ S, 0 ≤ E i) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ S, w i) :
    ∃ i ∈ S, 0 < w i ∧ E i * (∑ j ∈ S, w j) ≤ (∑ j ∈ S, E j) * w i := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨i, hi, hwi⟩ := (Finset.sum_pos_iff_of_nonneg hw).mp hW
  have hle : ∀ j ∈ S, (∑ k ∈ S, E k) * w j ≤ E j * (∑ k ∈ S, w k) := by
    intro j hj
    by_cases hwj : 0 < w j
    · exact (h j hj hwj).le
    · have hz : w j = 0 := le_antisymm (le_of_not_gt hwj) (hw j hj)
      rw [hz, mul_zero]
      exact mul_nonneg (hE j hj) hW.le
  have hlt := Finset.sum_lt_sum hle ⟨i, hi, h i hi hwi⟩
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hlt
  exact lt_irrefl _ hlt

end WangZahlLot.Obl.wz_kaufman_projection_count
