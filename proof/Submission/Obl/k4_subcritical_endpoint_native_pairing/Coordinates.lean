/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Coordinates.lean.
   Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_quadratic_selector_sweep.SignFibers

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

noncomputable section

open MvPolynomial

/-- The six-coefficient full-time predictor in the endpoint assertion. -/
def parameterPredictor (h : Fin 6 → ℝ) (t p q : ℝ) : ℝ :=
  h 0 + h 1 * t + (h 2 + h 3 * t) * p + (h 4 + h 5 * t) * q

/-- Derivative in the parameter-fiber direction `(1,2t)`. -/
def fiberSlope (h : Fin 6 → ℝ) (t : ℝ) : ℝ :=
  h 2 + h 3 * t + 2 * t * (h 4 + h 5 * t)

/-- An affine-parameter predictor with prescribed quadratic fiber derivative. -/
def correctionCoefficients (b : Fin 3 → ℝ) : Fin 6 → ℝ :=
  ![0, 0, b 0, b 1, 0, b 2 / 2]

theorem correction_fiberSlope (b : Fin 3 → ℝ) (t : ℝ) :
    fiberSlope (correctionCoefficients b) t = b 0 + b 1 * t + b 2 * t ^ 2 := by
  simp [fiberSlope, correctionCoefficients]
  ring

/-- Evaluation at `(0,R)` loses exactly the fiber derivative times `p`. -/
theorem parameterPredictor_fiber_identity (h : Fin 6 → ℝ) (t p q : ℝ) :
    parameterPredictor h t p q - parameterPredictor h t 0 (q - 2 * t * p) =
      p * fiberSlope h t := by
  dsimp [parameterPredictor, fiberSlope]
  ring

/-- Once the fiber derivative is small, scalar evaluation has the fitted accuracy. -/
theorem corrected_scalar_evaluation {h : Fin 6 → ℝ} {b : Fin 3 → ℝ}
    {t p q K w : ℝ} (hp : |p| ≤ K)
    (hf : |fiberSlope h t - (b 0 + b 1 * t + b 2 * t ^ 2)| ≤ w) :
    |(parameterPredictor h t p q - parameterPredictor (correctionCoefficients b) t p q) -
      (parameterPredictor h t 0 (q - 2 * t * p) -
        parameterPredictor (correctionCoefficients b) t 0 (q - 2 * t * p))| ≤ K * w := by
  have hid : (parameterPredictor h t p q - parameterPredictor (correctionCoefficients b) t p q) -
      (parameterPredictor h t 0 (q - 2 * t * p) -
        parameterPredictor (correctionCoefficients b) t 0 (q - 2 * t * p)) =
      p * (fiberSlope h t - fiberSlope (correctionCoefficients b) t) := by
    dsimp [parameterPredictor, fiberSlope]
    ring
  rw [hid, correction_fiberSlope, abs_mul]
  exact mul_le_mul hp hf (abs_nonneg _) ((abs_nonneg p).trans hp)

noncomputable def parameterPolynomial (h : Fin 6 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  C (h 0) + C (h 1) * X 0 +
    (C (h 2) + C (h 3) * X 0) * X 1 +
    (C (h 4) + C (h 5) * X 0) * X 2

theorem eval_parameterPolynomial (h : Fin 6 → ℝ) (t p q : ℝ) :
    eval ![t, p, q] (parameterPolynomial h) = parameterPredictor h t p q := by
  simp [parameterPolynomial, parameterPredictor]

theorem parameterPolynomial_degree (h : Fin 6 → ℝ) :
    (parameterPolynomial h).totalDegree ≤ 2 := by
  have hlin (a b : ℝ) : (C a + C b * X (0 : Fin 3)).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  have hterm (a b : ℝ) (i : Fin 3) :
      ((C a + C b * X (0 : Fin 3)) * X i).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add_right (hlin a b) 1)
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le ((hlin _ _).trans (by norm_num)) (hterm _ _ _)))
    (hterm _ _ _))

/-- Freeze the first static parameter and reconstruct the other as `Y+t*p`. -/
noncomputable def physicalParameterSubstitution (p : ℝ) : Fin 3 → MvPolynomial (Fin 2) ℝ :=
  ![X 0, C p, X 1 + C p * X 0]

theorem physicalParameterSubstitution_degree (p : ℝ) (i : Fin 3) :
    (physicalParameterSubstitution p i).totalDegree ≤ 1 := by
  fin_cases i
  · simp [physicalParameterSubstitution]
  · simp [physicalParameterSubstitution]
  · change (X (1 : Fin 2) + C p * X 0).totalDegree ≤ 1
    exact (totalDegree_add _ _).trans (max_le (by simp)
      ((totalDegree_mul _ _).trans (by simp)))

noncomputable def physicalParameterPolynomial (h : Fin 6 → ℝ) (p : ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  bind₁ (physicalParameterSubstitution p) (parameterPolynomial h)

theorem physicalParameterPolynomial_degree (h : Fin 6 → ℝ) (p : ℝ) :
    (physicalParameterPolynomial h p).totalDegree ≤ 2 :=
  (Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine _
    (physicalParameterSubstitution_degree p) _).trans (parameterPolynomial_degree h)

theorem eval_physicalParameterPolynomial (h : Fin 6 → ℝ) (p t Y : ℝ) :
    eval ![t, Y] (physicalParameterPolynomial h p) = parameterPredictor h t p (Y + t * p) := by
  rw [← eval_parameterPolynomial h t p (Y + t * p)]
  change eval₂Hom (RingHom.id ℝ) ![t, Y] _ = eval₂Hom (RingHom.id ℝ) _ _
  rw [physicalParameterPolynomial, eval₂Hom_bind₁]
  apply congrArg (fun f : Fin 3 → ℝ => eval₂Hom (RingHom.id ℝ) f (parameterPolynomial h))
  funext i
  fin_cases i <;> simp [physicalParameterSubstitution] <;> ring

/-- A normalized scalar parameter is affine in the physical coordinates after slicing. -/
noncomputable def scalarParameterSubstitution (D p p₀ q₀ : ℝ) :
    Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![X 0, C D⁻¹ * (X 1 - C q₀ + C (2 * p₀ - p) * X 0)]

theorem scalarParameterSubstitution_degree (D p p₀ q₀ : ℝ) (i : Fin 2) :
    (scalarParameterSubstitution D p p₀ q₀ i).totalDegree ≤ 1 := by
  fin_cases i
  · simp [scalarParameterSubstitution]
  · change (C D⁻¹ * (X 1 - C q₀ + C (2 * p₀ - p) * X 0) :
      MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_sub _ _).trans (max_le (by simp) (by simp))
    · exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C, totalDegree_X, zero_add]; omega)

noncomputable def returnedScalarPolynomial (F : MvPolynomial (Fin 2) ℝ)
    (D p p₀ q₀ : ℝ) : MvPolynomial (Fin 2) ℝ :=
  bind₁ (scalarParameterSubstitution D p p₀ q₀) F

theorem returnedScalarPolynomial_degree (F : MvPolynomial (Fin 2) ℝ)
    (D p p₀ q₀ : ℝ) :
    (returnedScalarPolynomial F D p p₀ q₀).totalDegree ≤ F.totalDegree :=
  Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine _
    (scalarParameterSubstitution_degree D p p₀ q₀) _

theorem eval_returnedScalarPolynomial (F : MvPolynomial (Fin 2) ℝ)
    (D p p₀ q₀ t Y : ℝ) :
    eval ![t, Y] (returnedScalarPolynomial F D p p₀ q₀) =
      eval ![t, (Y - q₀ + (2 * p₀ - p) * t) / D] F := by
  change eval₂Hom (RingHom.id ℝ) ![t, Y] _ = eval₂Hom (RingHom.id ℝ) _ F
  rw [returnedScalarPolynomial, eval₂Hom_bind₁]
  apply congrArg (fun f : Fin 2 → ℝ => eval₂Hom (RingHom.id ℝ) f F)
  funext i
  fin_cases i <;> simp [scalarParameterSubstitution, div_eq_mul_inv, mul_comm]

/-- The discrepancy between two endpoint fiber derivatives is quadratic in time. -/
def fiberTimePolynomial (h₀ h₁ : Fin 6 → ℝ) (D A : ℝ) : Polynomial ℝ :=
  Polynomial.C (D / A * (2 * (h₁ 5 - h₀ 5))) * Polynomial.X ^ 2 +
    Polynomial.C (D / A * (h₁ 3 - h₀ 3 + 2 * (h₁ 4 - h₀ 4))) * Polynomial.X +
    Polynomial.C (D / A * (h₁ 2 - h₀ 2))

theorem fiberTimePolynomial_degree (h₀ h₁ : Fin 6 → ℝ) (D A : ℝ) :
    (fiberTimePolynomial h₀ h₁ D A).natDegree ≤ 2 :=
  Polynomial.natDegree_quadratic_le

theorem eval_fiberTimePolynomial (h₀ h₁ : Fin 6 → ℝ) (D A t : ℝ) :
    (fiberTimePolynomial h₀ h₁ D A).eval t = D / A * (fiberSlope h₁ t - fiberSlope h₀ t) := by
  simp [fiberTimePolynomial, fiberSlope]
  ring

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing
