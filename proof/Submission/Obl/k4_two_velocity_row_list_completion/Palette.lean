import Submission.Obl.k4_row_cell_regularization.Palette

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace Submission.Obl.k4_two_velocity_row_list_completion

open Submission.Obl.k4_row_cell_regularization

/-- Palette cells whose left endpoints are near a point fit into a slightly larger
interval. This estimate only uses the original palette's interval cap. -/
theorem palette_near_cap (π : Measure ℝ) [IsProbabilityMeasure π]
    (D : Finset ℤ) {ξ K S r : ℝ} (hξ : 0 < ξ) (hK : 0 ≤ K)
    (hξr : ξ ≤ r) (hr1 : 2 * r ≤ 1)
    (hcap : ∀ x s : ℝ, ξ ≤ s → s ≤ 1 →
      π (Icc (x - s) (x + s)) ≤ ENNReal.ofReal (K * s ^ S)) (x : ℝ) :
    (∑ j ∈ D, if |binVel ξ j - x| < r then binWeight π ξ j else 0) ≤
      K * (2 * r) ^ S := by
  have hr : 0 < r := hξ.trans_le hξr
  rw [← Finset.sum_filter, sum_binWeight_eq hξ]
  have hsub : (⋃ j ∈ D.filter (fun j => |binVel ξ j - x| < r), velocityCell ξ j) ⊆
      Icc (x - 2 * r) (x + 2 * r) := by
    intro y hy
    obtain ⟨j, hj, hy⟩ := mem_iUnion₂.mp hy
    have hj' := abs_lt.mp (Finset.mem_filter.mp hj).2
    change -r < (j : ℝ) * ξ - x ∧ (j : ℝ) * ξ - x < r at hj'
    change (j : ℝ) * ξ ≤ y ∧ y < ((j : ℝ) + 1) * ξ at hy
    constructor <;> nlinarith
  have h := (measure_mono hsub).trans
    (hcap x (2 * r) (by linarith) hr1)
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ K * (2 * r) ^ S)]
    using hh

end Submission.Obl.k4_two_velocity_row_list_completion
