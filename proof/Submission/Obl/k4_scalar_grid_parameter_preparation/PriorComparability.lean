/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PriorComparability.lean -/
import Mathlib

/-! Lower product-density bounds persist under subpriors and later masks. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MeasureTheory
open scoped ENNReal

theorem inverse_scalar_measure_domination {Ω : Type*} [MeasurableSpace Ω]
    (σ μ : Measure Ω) (c : ℝ≥0∞) (hc₀ : c ≠ 0) (hct : c ≠ ∞) (h : c • σ ≤ μ) :
    σ ≤ c⁻¹ • μ := by
  apply Measure.le_iff.mpr
  intro A _
  change σ A ≤ c⁻¹ * μ A
  calc
    _ = c⁻¹ * (c * σ A) := by rw [← mul_assoc,ENNReal.inv_mul_cancel hc₀ hct,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl (h A)

theorem subprior_product_restriction_domination {X : Type*} [MeasurableSpace X]
    (θ ν : Measure X) (μ : Measure (X × ℝ)) (A E : Set (X × ℝ))
    (hEA : E ⊆ A) (hνθ : ν ≤ θ) (c : ℝ≥0∞) (hc₀ : c ≠ 0) (hct : c ≠ ∞)
    (hlo : c • (θ.prod volume).restrict A ≤ μ.restrict A) :
    (ν.prod volume).restrict E ≤ c⁻¹ • μ.restrict E := by
  have hh := Measure.restrict_mono_measure hlo E
  rw [Measure.restrict_smul,Measure.restrict_restrict_of_subset hEA,
    Measure.restrict_restrict_of_subset hEA] at hh
  exact (Measure.restrict_mono_measure (Measure.prod_mono hνθ le_rfl) E).trans
    (inverse_scalar_measure_domination _ _ c hc₀ hct hh)

end Submission.Obl.k4_scalar_grid_parameter_preparation
