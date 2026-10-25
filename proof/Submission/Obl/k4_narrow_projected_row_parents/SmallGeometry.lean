/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/SmallGeometry.lean.
   Earlier provenance comments in the source are retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.Model

namespace Submission.Obl.k4_narrow_projected_row_parents.Model

open Set

theorem floor_div_mem_Icc {x c B : ℝ} (hc : 0 < c) (hx : |x| ≤ B) :
    ⌊x / c⌋ ∈ Finset.Icc (-⌈B / c⌉ - 1) ⌈B / c⌉ := by
  rw [Finset.mem_Icc]
  rw [abs_le] at hx
  constructor
  · have h1 : -(B / c) ≤ x / c := by rw [← neg_div]; exact div_le_div_of_nonneg_right hx.1 hc.le
    have h2 : -(⌈B / c⌉ : ℝ) ≤ -(B / c) := neg_le_neg (Int.le_ceil _)
    have h3 : -(⌈B / c⌉ : ℝ) - 1 < x / c := by linarith
    have h4 : ((-⌈B / c⌉ - 1 : ℤ) : ℝ) ≤ x / c := by push_cast; linarith
    exact Int.le_floor.mpr h4
  · have h1 : x / c ≤ B / c := div_le_div_of_nonneg_right hx.2 hc.le
    exact Int.floor_le_iff.mpr (by linarith [Int.le_ceil (B / c)])

end Submission.Obl.k4_narrow_projected_row_parents.Model
