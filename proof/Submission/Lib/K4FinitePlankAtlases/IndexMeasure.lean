import Mathlib
/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
open scoped BigOperators

/-- A finite index law with its original nonnegative real weights. -/
noncomputable def indexMeasure {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    (ω : ι → ℝ) : Measure ι := ∑ i, (ω i).toNNReal • Measure.dirac i

theorem indexMeasure_finite {ι : Type*} [Fintype ι] [MeasurableSpace ι] (ω : ι → ℝ) :
    IsFiniteMeasure (indexMeasure ω) := by
  unfold indexMeasure
  infer_instance

/-- The mass on any set is the sum of the original weights it contains. -/
theorem indexMeasure_real_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (ω : ι → ℝ) (hω : ∀ i, 0 ≤ ω i) (S : Set ι) :
    (indexMeasure ω).real S = ∑ i, if i ∈ S then ω i else 0 := by
  classical
  unfold indexMeasure
  simp only [measureReal_def, Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum (fun i _ => by finiteness)]
  apply Finset.sum_congr rfl
  intro i _
  change (((ω i).toNNReal) • Measure.dirac i).real S = _
  rw [measureReal_nnreal_smul_apply]
  by_cases hi : i ∈ S <;>
    simp [measureReal_def, Measure.dirac_apply, hi, Real.toNNReal_of_nonneg (hω i)]

theorem indexMeasure_real_finset {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (ω : ι → ℝ)
    (hω : ∀ i, 0 ≤ ω i) (S : Set ι) :
    (indexMeasure ω).real S = ∑ i ∈ Finset.univ.filter (fun i => i ∈ S), ω i := by
  rw [indexMeasure_real_apply ω hω S, Finset.sum_filter]

end Submission.Lib.K4FinitePlankAtlases
