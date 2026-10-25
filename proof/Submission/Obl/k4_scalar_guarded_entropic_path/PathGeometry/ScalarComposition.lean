/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ScalarComposition.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ScalarEquiv

/-!
Finite scalar normalizations stay in the same quadratic graph family.
The formulas use the actual durations and widths, before taking limits.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MvPolynomial

/-- Two successive scalar coefficient normalizations compose to one
quadratic normalization in the original trajectory coordinates. -/
theorem normalizeScalarCoeff_comp
    (P Q : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (hQ : Q.totalDegree ≤ 2)
    (t₀ q₀ u₀ v₀ J₀ a₀ t₁ q₁ u₁ v₁ J₁ a₁ : ℝ)
    (hq₀ : q₀ ≠ 0) (hJ₀ : J₀ ≠ 0) (hJ₁ : J₁ ≠ 0)
    (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) (b : ScalarCoeff) :
    normalizeScalarCoeff Q t₁ q₁ u₁ v₁ J₁ a₁
        (normalizeScalarCoeff P t₀ q₀ u₀ v₀ J₀ a₀ b) =
      normalizeScalarCoeff (liftScalarPolynomial P Q t₀ q₀ u₀ v₀ J₀ a₀)
        (t₀ + q₀ * t₁) (q₀ * q₁)
        (u₀ + J₀ * u₁ - J₀ * v₁ * t₀ / q₀) (v₀ + J₀ * v₁ / q₀)
        (J₀ * J₁) (a₀ * a₁) b := by
  have hR := liftScalarPolynomial_degree P Q hP hQ t₀ q₀ u₀ v₀ J₀ a₀
  have hy (τ : ℝ) :
      scalarY (normalizeScalarCoeff Q t₁ q₁ u₁ v₁ J₁ a₁
        (normalizeScalarCoeff P t₀ q₀ u₀ v₀ J₀ a₀ b)) τ =
      scalarY (normalizeScalarCoeff (liftScalarPolynomial P Q t₀ q₀ u₀ v₀ J₀ a₀)
        (t₀ + q₀ * t₁) (q₀ * q₁)
        (u₀ + J₀ * u₁ - J₀ * v₁ * t₀ / q₀) (v₀ + J₀ * v₁ / q₀)
        (J₀ * J₁) (a₀ * a₁) b) τ := by
    rw [scalarY_normalize, scalarY_normalize, scalarY_normalize]
    have ht : t₀ + q₀ * (t₁ + q₁ * τ) = (t₀ + q₀ * t₁) + q₀ * q₁ * τ := by ring
    rw [ht]
    field_simp [hq₀, hJ₀, hJ₁]
    ring
  have hx (τ : ℝ) :
      scalarX (normalizeScalarCoeff Q t₁ q₁ u₁ v₁ J₁ a₁
        (normalizeScalarCoeff P t₀ q₀ u₀ v₀ J₀ a₀ b)) τ =
      scalarX (normalizeScalarCoeff (liftScalarPolynomial P Q t₀ q₀ u₀ v₀ J₀ a₀)
        (t₀ + q₀ * t₁) (q₀ * q₁)
        (u₀ + J₀ * u₁ - J₀ * v₁ * t₀ / q₀) (v₀ + J₀ * v₁ / q₀)
        (J₀ * J₁) (a₀ * a₁) b) τ := by
    rw [scalarX_normalize Q hQ, scalarX_normalize _ hR]
    simp only [normalizedSignal]
    rw [scalarX_normalize P hP, scalarY_normalize]
    simp only [normalizedSignal]
    rw [eval_liftScalarPolynomial]
    have ht : t₀ + q₀ * (t₁ + q₁ * τ) = (t₀ + q₀ * t₁) + q₀ * q₁ * τ := by ring
    have ht' : ((t₀ + q₀ * t₁) + q₀ * q₁ * τ - t₀) / q₀ = t₁ + q₁ * τ := by
      field_simp [hq₀]
      ring
    rw [ht, ht']
    field_simp [ha₀, ha₁]
    ring
  exact scalar_coeff_ext (hy 0) (hy 1) (hx 0) (hx 1) (hx (1 / 2))

/-- The actual full-space measurable equivalences obey the same original
coordinate composition law, with the quadratic lifted predictor. -/
theorem scalarTrajectoryEquiv_comp
    (P Q : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (hQ : Q.totalDegree ≤ 2)
    (t₀ q₀ u₀ v₀ J₀ a₀ t₁ q₁ u₁ v₁ J₁ a₁ : ℝ)
    (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0) (hJ₀ : J₀ ≠ 0) (hJ₁ : J₁ ≠ 0)
    (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) :
    (scalarTrajectoryEquiv P hP t₀ q₀ u₀ v₀ J₀ a₀ hq₀ hJ₀ ha₀).trans
        (scalarTrajectoryEquiv Q hQ t₁ q₁ u₁ v₁ J₁ a₁ hq₁ hJ₁ ha₁) =
      scalarTrajectoryEquiv (liftScalarPolynomial P Q t₀ q₀ u₀ v₀ J₀ a₀)
        (liftScalarPolynomial_degree P Q hP hQ t₀ q₀ u₀ v₀ J₀ a₀)
        (t₀ + q₀ * t₁) (q₀ * q₁)
        (u₀ + J₀ * u₁ - J₀ * v₁ * t₀ / q₀) (v₀ + J₀ * v₁ / q₀)
        (J₀ * J₁) (a₀ * a₁) (mul_ne_zero hq₀ hq₁)
        (mul_ne_zero hJ₀ hJ₁) (mul_ne_zero ha₀ ha₁) := by
  apply MeasurableEquiv.ext
  funext l
  change (l.1, normalizeScalarCoeff Q t₁ q₁ u₁ v₁ J₁ a₁
    (normalizeScalarCoeff P t₀ q₀ u₀ v₀ J₀ a₀ l.2)) = _
  exact congrArg (fun b => (l.1, b))
    (normalizeScalarCoeff_comp P Q hP hQ t₀ q₀ u₀ v₀ J₀ a₀ t₁ q₁ u₁ v₁ J₁ a₁
      hq₀ hJ₀ hJ₁ ha₀ ha₁ l.2)

/-- Successive actual time changes have the product duration and affine
original start, independently of all incidence restrictions. -/
theorem scalarTimeEquiv_comp (t₀ q₀ t₁ q₁ : ℝ) (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0) :
    (scalarTimeEquiv t₀ q₀ hq₀).trans (scalarTimeEquiv t₁ q₁ hq₁) =
      scalarTimeEquiv (t₀ + q₀ * t₁) (q₀ * q₁) (mul_ne_zero hq₀ hq₁) := by
  apply MeasurableEquiv.ext
  funext t
  change ((t - t₀) / q₀ - t₁) / q₁ = (t - (t₀ + q₀ * t₁)) / (q₀ * q₁)
  field_simp [hq₀, hq₁]
  ring

/-- The composed incidence map itself is one scalar normalization with a
quadratic predictor, including both full trajectory and actual time. -/
theorem scalarIncidenceEquiv_comp
    (P Q : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (hQ : Q.totalDegree ≤ 2)
    (t₀ q₀ u₀ v₀ J₀ a₀ t₁ q₁ u₁ v₁ J₁ a₁ : ℝ)
    (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0) (hJ₀ : J₀ ≠ 0) (hJ₁ : J₁ ≠ 0)
    (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) :
    (scalarIncidenceEquiv P hP t₀ q₀ u₀ v₀ J₀ a₀ hq₀ hJ₀ ha₀).trans
        (scalarIncidenceEquiv Q hQ t₁ q₁ u₁ v₁ J₁ a₁ hq₁ hJ₁ ha₁) =
      scalarIncidenceEquiv (liftScalarPolynomial P Q t₀ q₀ u₀ v₀ J₀ a₀)
        (liftScalarPolynomial_degree P Q hP hQ t₀ q₀ u₀ v₀ J₀ a₀)
        (t₀ + q₀ * t₁) (q₀ * q₁)
        (u₀ + J₀ * u₁ - J₀ * v₁ * t₀ / q₀) (v₀ + J₀ * v₁ / q₀)
        (J₀ * J₁) (a₀ * a₁) (mul_ne_zero hq₀ hq₁)
        (mul_ne_zero hJ₀ hJ₁) (mul_ne_zero ha₀ ha₁) := by
  apply MeasurableEquiv.ext
  funext z
  apply Prod.ext
  · exact congrArg (fun e : (ℕ × ScalarCoeff) ≃ᵐ (ℕ × ScalarCoeff) => e z.1)
      (scalarTrajectoryEquiv_comp P Q hP hQ t₀ q₀ u₀ v₀ J₀ a₀ t₁ q₁ u₁ v₁ J₁ a₁
        hq₀ hq₁ hJ₀ hJ₁ ha₀ ha₁)
  · exact congrArg (fun e : ℝ ≃ᵐ ℝ => e z.2) (scalarTimeEquiv_comp t₀ q₀ t₁ q₁ hq₀ hq₁)

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
