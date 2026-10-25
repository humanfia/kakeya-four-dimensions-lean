/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/ScalarEquiv.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ScalarCoordinates

/-! The whole-trajectory scalar normalization is an invertible measurable
coordinate change. This lets full-prior and incidence identities be composed
without choosing inverse maps on selected supports. -/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MvPolynomial

noncomputable section

/-- The hidden trajectory in the original coordinates, before recovering its
three coefficients. -/
def restoredSignal (P : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a : ℝ) (b : ScalarCoeff) (t : ℝ) : ℝ :=
  a * scalarX b ((t - t₀) / q) +
    eval ![t, u + t * v + J * scalarY b ((t - t₀) / q)] P

theorem restoredSignal_quadratic (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q u v J a : ℝ) (b : ScalarCoeff) :
    Submission.Obl.k4_eligibility_sign_description.Quadratic
      (restoredSignal P t₀ q u v J a b) := by
  obtain ⟨A, B, C, hpoly⟩ :=
    Submission.Obl.k4_eligibility_sign_description.Quadratic.mv_line P hP
      ![0, u + J * b 0 - J * t₀ * b 1 / q] ![1, v + J * b 1 / q]
  have heval (t : ℝ) :
      eval ![t, u + t * v + J * scalarY b ((t - t₀) / q)] P =
        A * t ^ 2 + B * t + C := by
    convert hpoly t using 2
    congr 1
    funext i
    fin_cases i <;> simp [scalarY] <;> ring
  refine ⟨a * b 4 / q ^ 2 + A,
    a * b 3 / q - 2 * a * t₀ * b 4 / q ^ 2 + B,
    a * b 2 - a * t₀ * b 3 / q + a * t₀ ^ 2 * b 4 / q ^ 2 + C, ?_⟩
  intro t
  unfold restoredSignal
  rw [heval]
  simp only [scalarX, div_eq_mul_inv]
  ring

/-- The inverse whole-trajectory change, including the old fitted quadratic. -/
def restoreScalarCoeff (P : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a : ℝ) (b : ScalarCoeff) : ScalarCoeff :=
  let f := restoredSignal P t₀ q u v J a b
  ![u + J * b 0 - J * t₀ * b 1 / q,
    v + J * b 1 / q,
    f 0,
    4 * f (1 / 2) - f 1 - 3 * f 0,
    2 * f 1 - 4 * f (1 / 2) + 2 * f 0]

theorem scalarY_restore (P : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a : ℝ) (b : ScalarCoeff) (t : ℝ) :
    scalarY (restoreScalarCoeff P t₀ q u v J a b) t =
      u + t * v + J * scalarY b ((t - t₀) / q) := by
  simp only [scalarY, restoreScalarCoeff, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem scalarX_restore (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q u v J a : ℝ) (b : ScalarCoeff) (t : ℝ) :
    scalarX (restoreScalarCoeff P t₀ q u v J a b) t =
      restoredSignal P t₀ q u v J a b t := by
  simpa [scalarX, restoreScalarCoeff] using
    (quadratic_interpolation_unit
      (restoredSignal_quadratic P hP t₀ q u v J a b) t).symm

/-- Every old trajectory is recovered, with no restriction to chart incidences. -/
theorem restore_normalizeScalarCoeff (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q u v J a : ℝ) (hq : q ≠ 0)
    (hJ : J ≠ 0) (ha : a ≠ 0) (b : ScalarCoeff) :
    restoreScalarCoeff P t₀ q u v J a
      (normalizeScalarCoeff P t₀ q u v J a b) = b := by
  have ht (t : ℝ) : t₀ + q * ((t - t₀) / q) = t := by field_simp; ring
  have hy (t : ℝ) :
      scalarY (restoreScalarCoeff P t₀ q u v J a
        (normalizeScalarCoeff P t₀ q u v J a b)) t = scalarY b t := by
    rw [scalarY_restore, scalarY_normalize, ht]
    field_simp
    ring
  have hx (t : ℝ) :
      scalarX (restoreScalarCoeff P t₀ q u v J a
        (normalizeScalarCoeff P t₀ q u v J a b)) t = scalarX b t := by
    rw [scalarX_restore P hP, restoredSignal, scalarX_normalize P hP,
      scalarY_normalize, normalizedSignal, ht]
    have hy' : u + t * v + J * ((scalarY b t - u - t * v) / J) = scalarY b t := by
      field_simp
      ring
    rw [hy']
    field_simp
    ring
  exact scalar_coeff_ext (hy 0) (hy 1) (hx 0) (hx 1) (hx (1 / 2))

/-- Every normalized trajectory is realized by a unique old trajectory. -/
theorem normalize_restoreScalarCoeff (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q u v J a : ℝ) (hq : q ≠ 0)
    (hJ : J ≠ 0) (ha : a ≠ 0) (b : ScalarCoeff) :
    normalizeScalarCoeff P t₀ q u v J a
      (restoreScalarCoeff P t₀ q u v J a b) = b := by
  have ht (t : ℝ) : (t₀ + q * t - t₀) / q = t := by field_simp; ring
  have hy (t : ℝ) :
      scalarY (normalizeScalarCoeff P t₀ q u v J a
        (restoreScalarCoeff P t₀ q u v J a b)) t = scalarY b t := by
    rw [scalarY_normalize, scalarY_restore, ht]
    field_simp
    ring
  have hx (t : ℝ) :
      scalarX (normalizeScalarCoeff P t₀ q u v J a
        (restoreScalarCoeff P t₀ q u v J a b)) t = scalarX b t := by
    rw [scalarX_normalize P hP, normalizedSignal, scalarX_restore P hP,
      scalarY_restore, restoredSignal, ht]
    field_simp
    ring
  exact scalar_coeff_ext (hy 0) (hy 1) (hx 0) (hx 1) (hx (1 / 2))

theorem continuous_normalizeScalarCoeff (P : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a : ℝ) : Continuous (normalizeScalarCoeff P t₀ q u v J a) := by
  have hsig (τ : ℝ) : Continuous (fun b => normalizedSignal P t₀ q a b τ) := by
    have heval : Continuous (fun b : ScalarCoeff =>
        eval ![t₀ + q * τ, scalarY b (t₀ + q * τ)] P) :=
      (MvPolynomial.continuous_eval P).comp (by unfold scalarY; fun_prop)
    unfold normalizedSignal
    exact ((by unfold scalarX; fun_prop :
      Continuous (fun b : ScalarCoeff => scalarX b (t₀ + q * τ))).sub heval).div_const a
  unfold normalizeScalarCoeff
  fun_prop

theorem continuous_restoreScalarCoeff (P : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a : ℝ) : Continuous (restoreScalarCoeff P t₀ q u v J a) := by
  have hsig (t : ℝ) : Continuous (fun b => restoredSignal P t₀ q u v J a b t) := by
    have heval : Continuous (fun b : ScalarCoeff =>
        eval ![t, u + t * v + J * scalarY b ((t - t₀) / q)] P) :=
      (MvPolynomial.continuous_eval P).comp (by unfold scalarY; fun_prop)
    unfold restoredSignal
    exact ((by unfold scalarX; fun_prop :
      Continuous (fun b : ScalarCoeff => a * scalarX b ((t - t₀) / q))).add heval)
  unfold restoreScalarCoeff
  fun_prop

/-- A scalar chart normalization gives a measurable equivalence of the full
five-coefficient trajectory space. -/
def scalarCoeffEquiv (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q u v J a : ℝ) (hq : q ≠ 0) (hJ : J ≠ 0) (ha : a ≠ 0) :
    ScalarCoeff ≃ᵐ ScalarCoeff where
  toFun := normalizeScalarCoeff P t₀ q u v J a
  invFun := restoreScalarCoeff P t₀ q u v J a
  left_inv := restore_normalizeScalarCoeff P hP t₀ q u v J a hq hJ ha
  right_inv := normalize_restoreScalarCoeff P hP t₀ q u v J a hq hJ ha
  measurable_toFun := (continuous_normalizeScalarCoeff P t₀ q u v J a).measurable
  measurable_invFun := (continuous_restoreScalarCoeff P t₀ q u v J a).measurable

/-- The internal copy index is preserved by normalization. -/
def scalarTrajectoryEquiv (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q u v J a : ℝ) (hq : q ≠ 0) (hJ : J ≠ 0) (ha : a ≠ 0) :
    (ℕ × ScalarCoeff) ≃ᵐ (ℕ × ScalarCoeff) :=
  (MeasurableEquiv.refl ℕ).prodCongr (scalarCoeffEquiv P hP t₀ q u v J a hq hJ ha)

/-- Affine normalization of time on the entire real line. -/
def scalarTimeEquiv (t₀ q : ℝ) (hq : q ≠ 0) : ℝ ≃ᵐ ℝ where
  toFun t := (t - t₀) / q
  invFun τ := t₀ + q * τ
  left_inv t := by field_simp; ring
  right_inv τ := by field_simp; ring
  measurable_toFun := by
    change Measurable (fun t : ℝ => (t - t₀) / q)
    fun_prop
  measurable_invFun := by
    change Measurable (fun τ : ℝ => t₀ + q * τ)
    fun_prop

/-- Normalization is a measurable equivalence before any incidence selection. -/
def scalarIncidenceEquiv (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q u v J a : ℝ) (hq : q ≠ 0) (hJ : J ≠ 0) (ha : a ≠ 0) :
    ((ℕ × ScalarCoeff) × ℝ) ≃ᵐ ((ℕ × ScalarCoeff) × ℝ) :=
  (scalarTrajectoryEquiv P hP t₀ q u v J a hq hJ ha).prodCongr (scalarTimeEquiv t₀ q hq)

/-- Full-trajectory coordinate identities determine the coefficient change
uniquely, even if its first description is an arbitrary measurable map. -/
theorem eq_scalarTrajectoryEquiv_of_identities
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ q u v J a : ℝ) (hq : q ≠ 0) (hJ : J ≠ 0) (ha : a ≠ 0)
    (θ : (ℕ × ScalarCoeff) → (ℕ × ScalarCoeff))
    (hcopy : ∀ l, (θ l).1 = l.1)
    (hy : ∀ l t, scalarY (θ l).2 ((t - t₀) / q) =
      (scalarY l.2 t - u - t * v) / J)
    (hx : ∀ l t, scalarX (θ l).2 ((t - t₀) / q) =
      (scalarX l.2 t - eval ![t, scalarY l.2 t] P) / a) :
    θ = scalarTrajectoryEquiv P hP t₀ q u v J a hq hJ ha := by
  funext l
  change θ l = (l.1, normalizeScalarCoeff P t₀ q u v J a l.2)
  refine Prod.ext ?_ ?_
  · exact hcopy l
  change (θ l).2 = normalizeScalarCoeff P t₀ q u v J a l.2
  have ht (τ : ℝ) : (t₀ + q * τ - t₀) / q = τ := by field_simp; ring
  have hy' (τ : ℝ) : scalarY (θ l).2 τ =
      scalarY (normalizeScalarCoeff P t₀ q u v J a l.2) τ := by
    rw [scalarY_normalize]
    simpa only [ht] using hy l (t₀ + q * τ)
  have hx' (τ : ℝ) : scalarX (θ l).2 τ =
      scalarX (normalizeScalarCoeff P t₀ q u v J a l.2) τ := by
    rw [scalarX_normalize P hP]
    simpa only [ht, normalizedSignal] using hx l (t₀ + q * τ)
  exact scalar_coeff_ext (hy' 0) (hy' 1) (hx' 0) (hx' 1) (hx' (1 / 2))

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
