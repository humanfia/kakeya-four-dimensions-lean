import Mathlib

/-!
The integral of the norm of a family of linear functionals is a seminorm, provided
the directional integrals exist. This packages the analytic part of polynomial
visibility separately from the construction of the high-visibility ensemble.
-/

namespace Submission.Obl.k4_prescribed_polynomial_visibility

open MeasureTheory
open scoped NNReal

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrating the norm of linear maps gives a seminorm. -/
noncomputable def integralSeminorm (μ : Measure X) (A : X → E →L[ℝ] F)
    (hA : ∀ v, Integrable (fun x => ‖A x v‖) μ) : Seminorm ℝ E :=
  Seminorm.of (fun v => ∫ x, ‖A x v‖ ∂μ)
    (fun v w => by
      calc
        (∫ x, ‖A x (v + w)‖ ∂μ) ≤ ∫ x, (‖A x v‖ + ‖A x w‖) ∂μ :=
          integral_mono (hA (v + w)) ((hA v).add (hA w))
            (fun x => by simpa only [map_add] using norm_add_le (A x v) (A x w))
        _ = (∫ x, ‖A x v‖ ∂μ) + ∫ x, ‖A x w‖ ∂μ := integral_add (hA v) (hA w))
    (fun a v => by
      simp_rw [map_smul, norm_smul]
      exact integral_const_mul _ _)

@[simp] theorem integralSeminorm_apply (μ : Measure X) (A : X → E →L[ℝ] F)
    (hA : ∀ v, Integrable (fun x => ‖A x v‖) μ) (v : E) :
    integralSeminorm μ A hA v = ∫ x, ‖A x v‖ ∂μ := rfl

/-- Real seminorms on finite-dimensional spaces are continuous. -/
theorem continuous_seminorm [FiniteDimensional ℝ E] (V : Seminorm ℝ E) : Continuous V := by
  exact continuousOn_univ.mp (V.convexOn.continuousOn isOpen_univ)

/-- The smooth polynomial function used to measure directional variation. -/
noncomputable def arctanPolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.arctan (MvPolynomial.eval (fun j => x j) p)

/-- Ambient variation on the radius-one ball about `c`. -/
noncomputable def polynomialVariation {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (c v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x in Metric.ball c 1, ‖fderiv ℝ (arctanPolynomial p) x v‖

theorem polynomialVariation_nonneg {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (c v : EuclideanSpace ℝ (Fin n)) : 0 ≤ polynomialVariation p c v :=
  integral_nonneg (fun _ => norm_nonneg _)

/-- Directional variation with its seminorm structure. -/
noncomputable def polynomialVariationSeminorm {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (c : EuclideanSpace ℝ (Fin n))
    (hp : ∀ v, IntegrableOn (fun x => ‖fderiv ℝ (arctanPolynomial p) x v‖)
      (Metric.ball c 1) volume) : Seminorm ℝ (EuclideanSpace ℝ (Fin n)) :=
  integralSeminorm (volume.restrict (Metric.ball c 1)) (fderiv ℝ (arctanPolynomial p)) hp

@[simp] theorem polynomialVariationSeminorm_apply {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (c : EuclideanSpace ℝ (Fin n))
    (hp : ∀ v, IntegrableOn (fun x => ‖fderiv ℝ (arctanPolynomial p) x v‖)
      (Metric.ball c 1) volume) (v : EuclideanSpace ℝ (Fin n)) :
    polynomialVariationSeminorm p c hp v = polynomialVariation p c v := rfl

/-- A finite nonnegative average, with the Euclidean regularizer included. -/
noncomputable def regularizedEnsemble {n r : ℕ} (p : Fin r → MvPolynomial (Fin n) ℝ)
    (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h) (c : EuclideanSpace ℝ (Fin n))
    (hp : ∀ h v, IntegrableOn (fun x => ‖fderiv ℝ (arctanPolynomial (p h)) x v‖)
      (Metric.ball c 1) volume) : Seminorm ℝ (EuclideanSpace ℝ (Fin n)) :=
  normSeminorm ℝ _ + ∑ h, (NNReal.mk (w h) (hw h)) • polynomialVariationSeminorm (p h) c (hp h)

@[simp] theorem regularizedEnsemble_apply {n r : ℕ} (p : Fin r → MvPolynomial (Fin n) ℝ)
    (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h) (c : EuclideanSpace ℝ (Fin n))
    (hp : ∀ h v, IntegrableOn (fun x => ‖fderiv ℝ (arctanPolynomial (p h)) x v‖)
      (Metric.ball c 1) volume) (v : EuclideanSpace ℝ (Fin n)) :
    regularizedEnsemble p w hw c hp v =
      ‖v‖ + ∑ h, w h * polynomialVariation (p h) c v := by
  simp [regularizedEnsemble, NNReal.smul_def]

theorem continuous_regularizedEnsemble {n r : ℕ} (p : Fin r → MvPolynomial (Fin n) ℝ)
    (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h) (c : EuclideanSpace ℝ (Fin n))
    (hp : ∀ h v, IntegrableOn (fun x => ‖fderiv ℝ (arctanPolynomial (p h)) x v‖)
      (Metric.ball c 1) volume) : Continuous (regularizedEnsemble p w hw c hp) :=
  continuous_seminorm _

theorem norm_le_regularizedEnsemble {n r : ℕ} (p : Fin r → MvPolynomial (Fin n) ℝ)
    (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h) (c : EuclideanSpace ℝ (Fin n))
    (hp : ∀ h v, IntegrableOn (fun x => ‖fderiv ℝ (arctanPolynomial (p h)) x v‖)
      (Metric.ball c 1) volume) (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ≤ regularizedEnsemble p w hw c hp v := by
  rw [regularizedEnsemble_apply]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun h _ =>
    mul_nonneg (hw h) (polynomialVariation_nonneg _ _ _)))

end Submission.Obl.k4_prescribed_polynomial_visibility
