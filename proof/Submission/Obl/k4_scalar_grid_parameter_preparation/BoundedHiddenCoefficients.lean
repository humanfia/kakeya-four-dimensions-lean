/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/BoundedHiddenCoefficients.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.HiddenCoefficientBalls
import Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing.LineGeometry

/-! A bounded coefficient map for clustering, equal to the original map on its full-measure core. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical

def boundedScalarHiddenCoefficients (B : ℝ) (a : Fin 5 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  if ∀ e, |a e| ≤ B then scalarHiddenCoefficients a else 0

theorem continuous_scalarHiddenCoefficients : Continuous scalarHiddenCoefficients := by
  unfold scalarHiddenCoefficients
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro e
  fin_cases e <;> simp <;> fun_prop

theorem measurable_boundedScalarHiddenCoefficients (B : ℝ) :
    Measurable (boundedScalarHiddenCoefficients B) := by
  have hG' : MeasurableSet (⋂ e : Fin 5, {a : Fin 5 → ℝ | |a e| ≤ B}) :=
    MeasurableSet.iInter fun e => measurableSet_le (measurable_pi_apply e).abs measurable_const
  have hG : MeasurableSet {a : Fin 5 → ℝ | ∀ e, |a e| ≤ B} := by
    convert hG' using 1
    ext a
    simp
  exact Measurable.ite hG continuous_scalarHiddenCoefficients.measurable measurable_const

theorem boundedScalarHiddenCoefficients_eq {B : ℝ} {a : Fin 5 → ℝ} (ha : ∀ e, |a e| ≤ B) :
    boundedScalarHiddenCoefficients B a = scalarHiddenCoefficients a := by
  simp only [boundedScalarHiddenCoefficients,ite_eq_left ha]

theorem norm_scalarHiddenCoefficients_le {B : ℝ} (hB : 0 ≤ B) {a : Fin 5 → ℝ}
    (ha : ∀ e, |a e| ≤ B) : ‖scalarHiddenCoefficients a‖ ≤ 3 * B := by
  apply Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing.norm_toLp_three_le hB
  intro e
  fin_cases e <;> exact ha _

theorem norm_boundedScalarHiddenCoefficients_le {B : ℝ} (hB : 0 ≤ B) (a : Fin 5 → ℝ) :
    ‖boundedScalarHiddenCoefficients B a‖ ≤ 3 * B := by
  by_cases ha : ∀ e, |a e| ≤ B
  · rw [boundedScalarHiddenCoefficients_eq ha]
    exact norm_scalarHiddenCoefficients_le hB ha
  · simp only [boundedScalarHiddenCoefficients,ha,ite_false,norm_zero]
    positivity

theorem boundedScalarHiddenCoefficients_ae_eq {X : Type*} [MeasurableSpace X]
    (θ : Measure X) (a : X → Fin 5 → ℝ) (B : ℝ)
    (hbounded : ∀ᵐ l ∂θ, ∀ e, |a l e| ≤ B) :
    (fun l => boundedScalarHiddenCoefficients B (a l)) =ᵐ[θ] fun l => scalarHiddenCoefficients (a l) :=
  hbounded.mono fun _ hl => boundedScalarHiddenCoefficients_eq hl

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
