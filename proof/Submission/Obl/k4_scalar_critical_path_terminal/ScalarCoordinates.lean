import Submission.Obl.k4_eligibility_sign_description.Families
import Submission.Obl.k4_quadratic_selector_sweep.SignFibers

/-!
Scalar coordinate changes and the lifting of quadratic graph tests in
the supplied paper, `lem:normalization`. Normalization is on the whole
time block; it does not condition trajectory coefficients on incidences.
-/

namespace Submission.Obl.k4_scalar_critical_path_terminal

open MvPolynomial

noncomputable section

abbrev ScalarCoeff := Fin 5 → ℝ

def scalarY (b : ScalarCoeff) (t : ℝ) : ℝ := b 0 + t * b 1

def scalarX (b : ScalarCoeff) (t : ℝ) : ℝ := b 2 + t * b 3 + t ^ 2 * b 4

/-- Three evaluations inside the unit interval recover a quadratic. -/
theorem quadratic_interpolation_unit {f : ℝ → ℝ}
    (hf : Submission.Obl.k4_eligibility_sign_description.Quadratic f) (t : ℝ) :
    f t = f 0 + t * (4 * f (1 / 2) - f 1 - 3 * f 0) +
      t ^ 2 * (2 * f 1 - 4 * f (1 / 2) + 2 * f 0) := by
  obtain ⟨A, B, C, hf⟩ := hf
  simp only [hf]
  ring

/-- Spatial positions and hidden positions at the three interpolation
times determine all five scalar trajectory coefficients. -/
theorem scalar_coeff_ext {a b : ScalarCoeff}
    (hy₀ : scalarY a 0 = scalarY b 0)
    (hy₁ : scalarY a 1 = scalarY b 1)
    (hx₀ : scalarX a 0 = scalarX b 0)
    (hx₁ : scalarX a 1 = scalarX b 1)
    (hxhalf : scalarX a (1 / 2) = scalarX b (1 / 2)) : a = b := by
  simp only [scalarY, scalarX] at *
  funext i
  fin_cases i <;> norm_num at * <;> linarith

/-- The normalized hidden coordinate before reading its coefficients. -/
def normalizedSignal (P : MvPolynomial (Fin 2) ℝ)
    (t₀ q a : ℝ) (b : ScalarCoeff) (τ : ℝ) : ℝ :=
  (scalarX b (t₀ + q * τ) -
    eval ![t₀ + q * τ, scalarY b (t₀ + q * τ)] P) / a

theorem normalizedSignal_quadratic (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q a : ℝ) (b : ScalarCoeff) :
    Submission.Obl.k4_eligibility_sign_description.Quadratic
      (normalizedSignal P t₀ q a b) := by
  obtain ⟨A, B, C, hpoly⟩ :=
    Submission.Obl.k4_eligibility_sign_description.Quadratic.mv_line
      P hP ![t₀, b 0 + t₀ * b 1] ![q, q * b 1]
  have heval (τ : ℝ) :
      eval ![t₀ + q * τ, scalarY b (t₀ + q * τ)] P =
        A * τ ^ 2 + B * τ + C := by
    convert hpoly τ using 2
    congr 1
    funext i
    fin_cases i <;> simp [scalarY] <;> ring
  refine ⟨(q ^ 2 * b 4 - A) / a,
    (q * (b 3 + 2 * t₀ * b 4) - B) / a,
    (b 2 + t₀ * b 3 + t₀ ^ 2 * b 4 - C) / a, ?_⟩
  intro τ
  simp only [normalizedSignal, heval, scalarX]
  ring

/-- Normalize time and space and subtract the old graph test. Hidden
coefficients are read at times zero, one half and one in the new block. -/
def normalizeScalarCoeff (P : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a : ℝ) (b : ScalarCoeff) : ScalarCoeff :=
  let f := normalizedSignal P t₀ q a b
  ![(b 0 + t₀ * b 1 - u - t₀ * v) / J,
    q * (b 1 - v) / J,
    f 0,
    4 * f (1 / 2) - f 1 - 3 * f 0,
    2 * f 1 - 4 * f (1 / 2) + 2 * f 0]

theorem scalarY_normalize (P : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a : ℝ) (b : ScalarCoeff) (τ : ℝ) :
    scalarY (normalizeScalarCoeff P t₀ q u v J a b) τ =
      (scalarY b (t₀ + q * τ) - u - (t₀ + q * τ) * v) / J := by
  simp only [scalarY, normalizeScalarCoeff, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem scalarX_normalize (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q u v J a : ℝ) (b : ScalarCoeff) (τ : ℝ) :
    scalarX (normalizeScalarCoeff P t₀ q u v J a b) τ =
      normalizedSignal P t₀ q a b τ := by
  simpa [scalarX, normalizeScalarCoeff] using
    (quadratic_interpolation_unit (normalizedSignal_quadratic P hP t₀ q a b) τ).symm

/-- Whole-block spatial and residual bounds control all new trajectory
coefficients by a fixed factor, independently of the old coefficient size. -/
theorem normalizeScalarCoeff_bound (P : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a K : ℝ) (b : ScalarCoeff) (hJ : 0 < J) (ha : 0 < a)
    (hK : 0 ≤ K)
    (hy : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |scalarY b (t₀ + q * τ) - u - (t₀ + q * τ) * v| ≤ K * J)
    (hx : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |scalarX b (t₀ + q * τ) -
        eval ![t₀ + q * τ, scalarY b (t₀ + q * τ)] P| ≤ K * a) :
    ∀ i, |normalizeScalarCoeff P t₀ q u v J a b i| ≤ 8 * K := by
  let b' := normalizeScalarCoeff P t₀ q u v J a b
  have hy' (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : |scalarY b' τ| ≤ K := by
    rw [scalarY_normalize, abs_div, abs_of_pos hJ]
    exact (div_le_iff₀ hJ).2 (hy τ hτ)
  have hx' (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
      |normalizedSignal P t₀ q a b τ| ≤ K := by
    rw [normalizedSignal, abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).2 (hx τ hτ)
  have hy₀ := abs_le.mp (hy' 0 (by norm_num))
  have hy₁ := abs_le.mp (hy' 1 (by norm_num))
  have hx₀ := abs_le.mp (hx' 0 (by norm_num))
  have hx₁ := abs_le.mp (hx' 1 (by norm_num))
  have hxhalf := abs_le.mp (hx' (1 / 2) (by norm_num))
  simp only [scalarY, zero_mul, add_zero, one_mul] at hy₀ hy₁
  intro i
  change |b' i| ≤ 8 * K
  fin_cases i
  · exact (abs_le.mpr hy₀).trans (by linarith)
  · change |b' 1| ≤ 8 * K
    apply abs_le.mpr
    constructor <;> linarith
  · change |normalizedSignal P t₀ q a b 0| ≤ 8 * K
    exact (abs_le.mpr hx₀).trans (by linarith)
  · change |4 * normalizedSignal P t₀ q a b (1 / 2) -
      normalizedSignal P t₀ q a b 1 - 3 * normalizedSignal P t₀ q a b 0| ≤ 8 * K
    apply abs_le.mpr
    constructor <;> linarith
  · change |2 * normalizedSignal P t₀ q a b 1 -
      4 * normalizedSignal P t₀ q a b (1 / 2) + 2 * normalizedSignal P t₀ q a b 0| ≤ 8 * K
    apply abs_le.mpr
    constructor <;> linarith

/-- Affine substitutions used to lift a normalized child polynomial. -/
def scalarNormalizationSubstitution (t₀ q u v J : ℝ) :
    Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![(X 0 - C t₀) * C q⁻¹, (X 1 - C u - X 0 * C v) * C J⁻¹]

theorem scalarNormalizationSubstitution_degree (t₀ q u v J : ℝ) (i : Fin 2) :
    (scalarNormalizationSubstitution t₀ q u v J i).totalDegree ≤ 1 := by
  have hx (i : Fin 2) : (X i : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by simp
  have hc (c : ℝ) : (C c : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by simp
  have hmul (Q : MvPolynomial (Fin 2) ℝ) (c : ℝ) :
      (Q * C c).totalDegree ≤ Q.totalDegree := by
    simpa using totalDegree_mul Q (C c)
  fin_cases i
  · exact (hmul _ _).trans ((totalDegree_sub _ _).trans (max_le (hx 0) (hc t₀)))
  · exact (hmul _ _).trans ((totalDegree_sub _ _).trans
      (max_le ((totalDegree_sub _ _).trans (max_le (hx 1) (hc u)))
        ((hmul _ _).trans (hx 0))))

/-- The lifted test still has the special scalar form `x - quadratic`. -/
def liftScalarPolynomial (P Q : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a : ℝ) : MvPolynomial (Fin 2) ℝ :=
  P + C a * bind₁ (scalarNormalizationSubstitution t₀ q u v J) Q

theorem liftScalarPolynomial_degree (P Q : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (hQ : Q.totalDegree ≤ 2) (t₀ q u v J a : ℝ) :
    (liftScalarPolynomial P Q t₀ q u v J a).totalDegree ≤ 2 := by
  apply (totalDegree_add _ _).trans
  apply max_le hP
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact (Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine _
    (scalarNormalizationSubstitution_degree t₀ q u v J) Q).trans hQ

theorem eval_liftScalarPolynomial (P Q : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a t y : ℝ) :
    eval ![t, y] (liftScalarPolynomial P Q t₀ q u v J a) =
      eval ![t, y] P + a * eval ![(t - t₀) / q, (y - u - t * v) / J] Q := by
  simp only [liftScalarPolynomial, eval_add, eval_mul, eval_C]
  congr 2
  change eval₂Hom (RingHom.id ℝ) ![t, y] _ = eval₂Hom (RingHom.id ℝ) _ Q
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin 2 → ℝ => eval₂Hom (RingHom.id ℝ) f Q)
  funext i
  fin_cases i <;> simp [scalarNormalizationSubstitution, div_eq_mul_inv]

/-- The old residual is exactly the hidden scale times the new residual. -/
theorem residual_liftScalarPolynomial (P Q : MvPolynomial (Fin 2) ℝ)
    (t₀ q u v J a t y x : ℝ) (ha : a ≠ 0) :
    x - eval ![t, y] (liftScalarPolynomial P Q t₀ q u v J a) =
      a * ((x - eval ![t, y] P) / a -
        eval ![(t - t₀) / q, (y - u - t * v) / J] Q) := by
  rw [eval_liftScalarPolynomial]
  field_simp
  ring

/-- Lifting preserves a child residual estimate on the entire parent
block, with precisely the parent hidden-coordinate scale as factor. -/
theorem whole_block_fit_lift (P Q : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q u v J a B : ℝ) (b : ScalarCoeff)
    (hq : 0 < q) (ha : 0 < a)
    (hfit : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |scalarX (normalizeScalarCoeff P t₀ q u v J a b) τ -
        eval ![τ, scalarY (normalizeScalarCoeff P t₀ q u v J a b) τ] Q| ≤ B) :
    ∀ t ∈ Set.Icc t₀ (t₀ + q),
      |scalarX b t - eval ![t, scalarY b t]
        (liftScalarPolynomial P Q t₀ q u v J a)| ≤ a * B := by
  intro t ht
  let τ := (t - t₀) / q
  have hτ : τ ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr ht.1) hq.le, ?_⟩
    exact (div_le_one hq).2 (by linarith [ht.2])
  have htτ : t₀ + q * τ = t := by dsimp [τ]; field_simp; ring
  have hfit' := hfit τ hτ
  rw [scalarX_normalize P hP, scalarY_normalize, htτ] at hfit'
  rw [residual_liftScalarPolynomial P Q t₀ q u v J a t (scalarY b t)
    (scalarX b t) ha.ne', abs_mul, abs_of_pos ha]
  exact mul_le_mul_of_nonneg_left (by simpa [normalizedSignal, htτ, τ] using hfit') ha.le

end

end Submission.Obl.k4_scalar_critical_path_terminal
