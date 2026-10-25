import Submission.Obl.k4_prescribed_polynomial_visibility.VariationSeminorm

namespace Submission.Obl.k4_prescribed_polynomial_visibility

open MeasureTheory

/-- Real multivariate polynomials are smooth on Euclidean space. -/
theorem contDiff_polynomial_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (k : WithTop ℕ∞) :
    ContDiff ℝ k (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => x j) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ k (fun _ : EuclideanSpace ℝ (Fin n) => a))
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p j hp => simpa using hp.mul (EuclideanSpace.proj j).contDiff

/-- Composing with arctangent preserves smoothness. -/
theorem contDiff_arctanPolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (k : WithTop ℕ∞) : ContDiff ℝ k (arctanPolynomial p) :=
  Real.contDiff_arctan.comp (contDiff_polynomial_eval p k)

/-- Every local directional integral exists, in every dimension. -/
theorem integrableOn_polynomialVariation {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (c v : EuclideanSpace ℝ (Fin n)) :
    IntegrableOn (fun x => ‖fderiv ℝ (arctanPolynomial p) x v‖)
      (Metric.ball c 1) volume := by
  have h : Continuous (fun x => ‖fderiv ℝ (arctanPolynomial p) x v‖) :=
    (((contDiff_arctanPolynomial p 1).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).norm
  exact (h.continuousOn.integrableOn_compact (isCompact_closedBall c 1)).mono_set
    Metric.ball_subset_closedBall

/-- The canonical regularized ensemble, using smoothness for integrability. -/
noncomputable def ensemble {n r : ℕ} (p : Fin r → MvPolynomial (Fin n) ℝ)
    (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h) (c : EuclideanSpace ℝ (Fin n)) :
    Seminorm ℝ (EuclideanSpace ℝ (Fin n)) :=
  regularizedEnsemble p w hw c (fun h => integrableOn_polynomialVariation (p h) c)

@[simp] theorem ensemble_apply {n r : ℕ} (p : Fin r → MvPolynomial (Fin n) ℝ)
    (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h) (c v : EuclideanSpace ℝ (Fin n)) :
    ensemble p w hw c v = ‖v‖ + ∑ h, w h * polynomialVariation (p h) c v :=
  regularizedEnsemble_apply _ _ _ _ _ _

theorem continuous_ensemble {n r : ℕ} (p : Fin r → MvPolynomial (Fin n) ℝ)
    (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h) (c : EuclideanSpace ℝ (Fin n)) :
    Continuous (ensemble p w hw c) := continuous_seminorm _

theorem norm_le_ensemble {n r : ℕ} (p : Fin r → MvPolynomial (Fin n) ℝ)
    (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h) (c v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ≤ ensemble p w hw c v := norm_le_regularizedEnsemble _ _ _ _ _ _

end Submission.Obl.k4_prescribed_polynomial_visibility
