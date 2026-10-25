import Mathlib

/-! Count visited cells with their original whole-cell witnesses. The
surviving residual measure is not required to retain the original floor. -/

open MeasureTheory Set

namespace Submission.Obl.k4_initial_horizon_bound

/-- Original whole-cell masses bound the number of good cells. -/
theorem original_cell_count_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → ι) (hcode : Measurable code)
    (F : Finset ι) {a : ℝ} (hfloor : ∀ z ∈ F, a ≤ μ.real (code ⁻¹' {z})) :
    a * (F.card : ℝ) ≤ μ.real univ := by
  calc
    a * (F.card : ℝ) = ∑ _z ∈ F, a := by simp [mul_comm]
    _ ≤ ∑ z ∈ F, μ.real (code ⁻¹' {z}) := Finset.sum_le_sum hfloor
    _ ≤ μ.real univ := sum_measureReal_le_measureReal_univ
      (fun z _ => hcode (measurableSet_singleton z))
      (fun z _ z' _ hzz' => Disjoint.preimage _ (disjoint_singleton.mpr hzz'))

theorem original_cell_card_le {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → ι) (hcode : Measurable code)
    (F : Finset ι) {a : ℝ} (ha : 0 < a)
    (hfloor : ∀ z ∈ F, a ≤ μ.real (code ⁻¹' {z})) :
    (F.card : ℝ) ≤ μ.real univ / a := by
  apply (le_div_iff₀ ha).mpr
  simpa only [mul_comm] using original_cell_count_bound μ code hcode F hfloor

end Submission.Obl.k4_initial_horizon_bound
