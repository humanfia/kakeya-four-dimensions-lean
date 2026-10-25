/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Normalizing a finite original incidence law scales its actual line
marginal by the same denominator and leaves its time kernel unchanged. -/
theorem original_incidence_normalization {L T : Type*}
    [MeasurableSpace L] [MeasurableSpace T]
    (μ : Measure (L × T)) [IsFiniteMeasure μ]
    (κ : Kernel L T) [IsMarkovKernel κ]
    (hjoint : μ.fst ⊗ₘ κ = μ) (hpositive : 0 < μ univ) :
    IsProbabilityMeasure ((μ univ)⁻¹ • μ) ∧
      IsProbabilityMeasure ((μ univ)⁻¹ • μ.fst) ∧
      ((μ univ)⁻¹ • μ.fst) ⊗ₘ κ = (μ univ)⁻¹ • μ := by
  have hm : μ univ ≠ ∞ := measure_ne_top μ univ
  have hP : IsProbabilityMeasure ((μ univ)⁻¹ • μ) := by
    constructor
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hpositive.ne' hm
  have hν : IsProbabilityMeasure ((μ univ)⁻¹ • μ.fst) := by
    constructor
    rw [Measure.smul_apply,smul_eq_mul,Measure.fst_univ]
    exact ENNReal.inv_mul_cancel hpositive.ne' hm
  refine ⟨hP,hν,?_⟩
  rw [Measure.compProd_smul_left,hjoint]

end Submission.Lib.K4PolynomialNorming
