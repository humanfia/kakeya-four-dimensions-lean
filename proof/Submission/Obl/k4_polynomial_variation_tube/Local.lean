import Mathlib
import ChallengeDeps
open MeasureTheory

namespace Submission.Obl.k4_polynomial_variation_tube

variable {n : ℕ}

lemma contDiff_polynomial_eval (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ⊤ (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => y j) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (contDiff_const : ContDiff ℝ ⊤ (fun _ : EuclideanSpace ℝ (Fin n) => c))
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p j hp =>
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    apply hp.mul
    exact ((ContinuousLinearMap.proj j).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap).contDiff

lemma continuous_directional_variation (p : MvPolynomial (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        Real.arctan (MvPolynomial.eval (fun j => y j) p)) x) v‖) := by
  exact (((Real.contDiff_arctan.comp (contDiff_polynomial_eval p)).continuous_fderiv
    (by simp)).clm_apply continuous_const).norm

lemma integrableOn_directional_variation (p : MvPolynomial (Fin n) ℝ)
    (c v : EuclideanSpace ℝ (Fin n)) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        Real.arctan (MvPolynomial.eval (fun j => y j) p)) x) v‖)
      (Metric.ball c 1) volume := by
  exact ((continuous_directional_variation p v).continuousOn.integrableOn_compact
    (isCompact_closedBall c 1)).mono_set Metric.ball_subset_closedBall

end Submission.Obl.k4_polynomial_variation_tube
