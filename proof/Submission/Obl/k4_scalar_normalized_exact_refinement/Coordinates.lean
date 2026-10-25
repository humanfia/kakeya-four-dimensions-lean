import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces
import Submission.Lib.K4PolynomialPotential.TrajectoryFits

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory

noncomputable section

abbrev Line := ℕ × (Fin 5 → ℝ)
abbrev y := k4_scalar_linear_critical_extremizers.Split.y
abbrev x := k4_scalar_linear_critical_extremizers.Split.x

/-- The interpolation formula at `0`, `1/2`, and `1` for a quadratic. -/
lemma quadratic_interpolation (p : Polynomial ℝ) (hp : p.natDegree ≤ 2) (t : ℝ) :
    p.eval t = p.eval 0 + t * (4 * p.eval (1 / 2) - p.eval 1 - 3 * p.eval 0) +
      t ^ 2 * (2 * (p.eval 1 - 2 * p.eval (1 / 2) + p.eval 0)) := by
  have h (s : ℝ) : p.eval s = p.coeff 0 + p.coeff 1 * s + p.coeff 2 * s ^ 2 := by
    rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
    norm_num [Finset.sum_range_succ]
  rw [h t, h 0, h (1 / 2), h 1]
  ring

/-- The original quadratic residual along a whole trajectory. -/
def residual (P : MvPolynomial (Fin 2) ℝ) (l : Line) : Polynomial ℝ :=
  Polynomial.C (l.2 2) + Polynomial.C (l.2 3) * Polynomial.X +
    Polynomial.C (l.2 4) * Polynomial.X ^ 2 -
    Submission.Lib.K4PolynomialPotential.scalarLineHom (l.2 0) (l.2 1) P

lemma eval_residual (P : MvPolynomial (Fin 2) ℝ) (l : Line) (t : ℝ) :
    (residual P l).eval t = x l t - MvPolynomial.eval ![t, y l t] P := by
  simp [residual, x, y, k4_scalar_linear_critical_extremizers.Split.x,
    k4_scalar_linear_critical_extremizers.Split.y,
    Submission.Lib.K4PolynomialPotential.eval_scalarLineHom]
  ring

lemma natDegree_residual_le (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (l : Line) : (residual P l).natDegree ≤ 2 := by
  unfold residual
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · exact Polynomial.natDegree_mul_le.trans (by simp)
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  · exact (Submission.Lib.K4PolynomialPotential.natDegree_scalarLineHom_le P _ _).trans hP

/-- The scalar affine chart map, defined by trajectory interpolation. -/
def normalizeLine (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ)
    (l : Line) : Line :=
  let R := fun s : ℝ => (x l (t₀ + dt * s) -
    MvPolynomial.eval ![t₀ + dt * s, y l (t₀ + dt * s)] P) / δ
  (l.1, ![(y l t₀ - u - t₀ * v) / J, dt * (l.2 1 - v) / J,
    R 0, 4 * R (1 / 2) - R 1 - 3 * R 0,
    2 * (R 1 - 2 * R (1 / 2) + R 0)])

lemma normalizeLine_label (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ)
    (l : Line) : (normalizeLine P t₀ dt u v J δ l).1 = l.1 := rfl

lemma y_normalizeLine (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ)
    (l : Line) (t : ℝ) :
    y (normalizeLine P t₀ dt u v J δ l) t =
      (y l (t₀ + dt * t) - u - (t₀ + dt * t) * v) / J := by
  simp only [y, k4_scalar_linear_critical_extremizers.Split.y, normalizeLine,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma x_normalizeLine (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (l : Line) (t : ℝ) :
    x (normalizeLine P t₀ dt u v J δ l) t =
      (x l (t₀ + dt * t) -
        MvPolynomial.eval ![t₀ + dt * t, y l (t₀ + dt * t)] P) / δ := by
  let p := (residual P l).comp (Polynomial.C t₀ + Polynomial.C dt * Polynomial.X)
  have hlin : (Polynomial.C t₀ + Polynomial.C dt * Polynomial.X).natDegree ≤ 1 :=
    Polynomial.natDegree_add_le_of_degree_le (by simp)
      (Polynomial.natDegree_mul_le.trans (by simp))
  have hp : p.natDegree ≤ 2 := by
    exact Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul (natDegree_residual_le P hP l) hlin).trans (by norm_num))
  have he (s : ℝ) : p.eval s = x l (t₀ + dt * s) -
      MvPolynomial.eval ![t₀ + dt * s, y l (t₀ + dt * s)] P := by
    simp [p, Polynomial.eval_comp, eval_residual]
  change (x l (t₀ + dt * 0) - _) / δ +
    t * (4 * ((x l (t₀ + dt * (1 / 2)) - _) / δ) -
      (x l (t₀ + dt * 1) - _) / δ - 3 * ((x l (t₀ + dt * 0) - _) / δ)) +
    t ^ 2 * (2 * ((x l (t₀ + dt * 1) - _) / δ -
      2 * ((x l (t₀ + dt * (1 / 2)) - _) / δ) +
      (x l (t₀ + dt * 0) - _) / δ)) = _
  simp only [← he]
  rw [quadratic_interpolation p hp t]
  ring

lemma continuous_normalizeLine (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ) :
    Continuous (normalizeLine P t₀ dt u v J δ) := by
  have hy (s : ℝ) : Continuous (fun l : Line => y l s) := by
    dsimp [y, k4_scalar_linear_critical_extremizers.Split.y]
    fun_prop
  have hx (s : ℝ) : Continuous (fun l : Line => x l s) := by
    dsimp [x, k4_scalar_linear_critical_extremizers.Split.x]
    fun_prop
  have hP (s : ℝ) : Continuous (fun l : Line => MvPolynomial.eval ![s, y l s] P) := by
    apply (MvPolynomial.continuous_eval P).comp
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using (continuous_const : Continuous (fun _ : Line => s))
    · simpa using hy s
  apply continuous_fst.prodMk
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [normalizeLine] <;> fun_prop

lemma measurable_normalizeLine (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ) :
    Measurable (normalizeLine P t₀ dt u v J δ) :=
  (continuous_normalizeLine P t₀ dt u v J δ).measurable

lemma y_normalizeLine_at (P : MvPolynomial (Fin 2) ℝ) (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (l : Line) (t : ℝ) :
    y (normalizeLine P t₀ dt u v J δ l) ((t - t₀) / dt) =
      (y l t - u - t * v) / J := by
  rw [y_normalizeLine]
  have ht : t₀ + dt * ((t - t₀) / dt) = t := by field_simp; ring
  rw [ht]

lemma x_normalizeLine_at (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (l : Line) (t : ℝ) :
    x (normalizeLine P t₀ dt u v J δ l) ((t - t₀) / dt) =
      (x l t - MvPolynomial.eval ![t, y l t] P) / δ := by
  rw [x_normalizeLine P hP]
  have ht : t₀ + dt * ((t - t₀) / dt) = t := by field_simp; ring
  rw [ht]

/-- The label and the two whole trajectories determine a line. -/
lemma line_ext {l l' : Line} (hlabel : l.1 = l'.1)
    (hy : ∀ t, y l t = y l' t) (hx : ∀ t, x l t = x l' t) : l = l' := by
  apply Prod.ext hlabel
  have hy0 := hy 0
  have hy1 := hy 1
  have hx0 := hx 0
  have hx1 := hx 1
  have hxm := hx (-1)
  simp only [y, x, k4_scalar_linear_critical_extremizers.Split.y,
    k4_scalar_linear_critical_extremizers.Split.x] at *
  have h0 : l.2 0 = l'.2 0 := by simpa using hy0
  have h1 : l.2 1 = l'.2 1 := by nlinarith [hy1]
  have h2 : l.2 2 = l'.2 2 := by simpa using hx0
  have h3 : l.2 3 = l'.2 3 := by nlinarith [hx1, hxm]
  have h4 : l.2 4 = l'.2 4 := by nlinarith [hx1, hxm]
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

lemma normalizeLine_injective (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) :
    Function.Injective (normalizeLine P t₀ dt u v J δ) := by
  intro l l' hll
  have hy : ∀ t, y l t = y l' t := by
    intro t
    have h := congrArg (fun m : Line => y m ((t - t₀) / dt)) hll
    rw [y_normalizeLine_at _ _ _ _ _ _ _ hdt,
      y_normalizeLine_at _ _ _ _ _ _ _ hdt] at h
    have hh := (div_left_inj' hJ).mp h
    linarith
  have hl : l.1 = l'.1 := by
    change (normalizeLine P t₀ dt u v J δ l).1 =
      (normalizeLine P t₀ dt u v J δ l').1
    exact congrArg Prod.fst hll
  apply line_ext hl hy
  intro t
  have h := congrArg (fun m : Line => x m ((t - t₀) / dt)) hll
  rw [x_normalizeLine_at _ hP _ _ _ _ _ _ hdt,
    x_normalizeLine_at _ hP _ _ _ _ _ _ hdt, hy] at h
  have hh := (div_left_inj' hδ).mp h
  linarith

lemma y_shearLine (P : MvPolynomial (Fin 2) ℝ) (l : Line) (t : ℝ) :
    y (normalizeLine P 0 1 0 0 1 1 l) t = y l t := by
  simpa using y_normalizeLine P 0 1 0 0 1 1 l t

lemma x_shearLine (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (l : Line) (t : ℝ) :
    x (normalizeLine P 0 1 0 0 1 1 l) t =
      x l t - MvPolynomial.eval ![t, y l t] P := by
  simpa using x_normalizeLine P hP 0 1 0 0 1 1 l t

/-- Subtracting the predictor is an invertible polynomial change of line coordinates. -/
def shearEquiv (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) : Line ≃ᵐ Line where
  toFun := normalizeLine P 0 1 0 0 1 1
  invFun := normalizeLine (-P) 0 1 0 0 1 1
  left_inv l := by
    apply line_ext
    · rfl
    · intro t
      rw [y_shearLine, y_shearLine]
    · intro t
      rw [x_shearLine (-P) (by simpa using hP), x_shearLine P hP, y_shearLine]
      simp
  right_inv l := by
    apply line_ext
    · rfl
    · intro t
      rw [y_shearLine, y_shearLine]
    · intro t
      rw [x_shearLine P hP, x_shearLine (-P) (by simpa using hP), y_shearLine]
      simp
  measurable_toFun := measurable_normalizeLine P 0 1 0 0 1 1
  measurable_invFun := measurable_normalizeLine (-P) 0 1 0 0 1 1

lemma affine_normalize_left_inv (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) (l : Line) :
    normalizeLine 0 (-t₀ / dt) dt⁻¹ (-(u + t₀ * v) / J) (-dt * v / J) J⁻¹ δ⁻¹
      (normalizeLine 0 t₀ dt u v J δ l) = l := by
  apply line_ext
  · rfl
  · intro t
    rw [y_normalizeLine, y_normalizeLine]
    dsimp [y, k4_scalar_linear_critical_extremizers.Split.y]
    field_simp
    ring
  · intro t
    rw [x_normalizeLine 0 (by simp), x_normalizeLine 0 (by simp)]
    simp only [map_zero, sub_zero]
    dsimp [x, k4_scalar_linear_critical_extremizers.Split.x]
    field_simp
    ring

lemma affine_normalize_right_inv (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) (l : Line) :
    normalizeLine 0 t₀ dt u v J δ
      (normalizeLine 0 (-t₀ / dt) dt⁻¹ (-(u + t₀ * v) / J) (-dt * v / J) J⁻¹ δ⁻¹ l) = l := by
  apply line_ext
  · rfl
  · intro t
    rw [y_normalizeLine, y_normalizeLine]
    dsimp [y, k4_scalar_linear_critical_extremizers.Split.y]
    field_simp
    ring
  · intro t
    rw [x_normalizeLine 0 (by simp), x_normalizeLine 0 (by simp)]
    simp only [map_zero, sub_zero]
    dsimp [x, k4_scalar_linear_critical_extremizers.Split.x]
    field_simp
    ring

/-- The affine change of time and scales is a measurable equivalence. -/
def affineNormalizeEquiv (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) : Line ≃ᵐ Line where
  toFun := normalizeLine 0 t₀ dt u v J δ
  invFun := normalizeLine 0 (-t₀ / dt) dt⁻¹ (-(u + t₀ * v) / J) (-dt * v / J) J⁻¹ δ⁻¹
  left_inv := affine_normalize_left_inv t₀ dt u v J δ hdt hJ hδ
  right_inv := affine_normalize_right_inv t₀ dt u v J δ hdt hJ hδ
  measurable_toFun := measurable_normalizeLine 0 t₀ dt u v J δ
  measurable_invFun := measurable_normalizeLine 0 (-t₀ / dt) dt⁻¹
    (-(u + t₀ * v) / J) (-dt * v / J) J⁻¹ δ⁻¹

/-- The full scalar chart coordinate change. -/
def normalizeEquiv (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) : Line ≃ᵐ Line :=
  (shearEquiv P hP).trans (affineNormalizeEquiv t₀ dt u v J δ hdt hJ hδ)

lemma normalizeEquiv_apply (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) (l : Line) :
    normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ l = normalizeLine P t₀ dt u v J δ l := by
  change normalizeLine 0 t₀ dt u v J δ (normalizeLine P 0 1 0 0 1 1 l) = _
  apply line_ext
  · rfl
  · intro t
    rw [y_normalizeLine, y_shearLine, y_normalizeLine]
  · intro t
    rw [x_normalizeLine 0 (by simp), x_shearLine P hP, x_normalizeLine P hP]
    simp

/-- A bound on the whole unit-time trajectories bounds every coefficient. -/
lemma coefficients_bound_of_trajectories (l : Line) {R : ℝ} (hR : 0 ≤ R)
    (hy : ∀ t ∈ Set.Icc (0 : ℝ) 1, |y l t| ≤ R)
    (hx : ∀ t ∈ Set.Icc (0 : ℝ) 1, |x l t| ≤ R) :
    ∀ i, |l.2 i| ≤ 8 * R := by
  have hy0 := abs_le.mp (hy 0 (by norm_num))
  have hy1 := abs_le.mp (hy 1 (by norm_num))
  have hx0 := abs_le.mp (hx 0 (by norm_num))
  have hxh := abs_le.mp (hx (1 / 2) (by norm_num))
  have hx1 := abs_le.mp (hx 1 (by norm_num))
  norm_num [y, x, k4_scalar_linear_critical_extremizers.Split.y,
    k4_scalar_linear_critical_extremizers.Split.x] at hy0 hy1 hx0 hxh hx1
  have h0 : |l.2 0| ≤ 8 * R := abs_le.mpr ⟨by linarith, by linarith⟩
  have h1 : |l.2 1| ≤ 8 * R := abs_le.mpr ⟨by linarith, by linarith⟩
  have h2 : |l.2 2| ≤ 8 * R := abs_le.mpr ⟨by linarith, by linarith⟩
  have h3 : |l.2 3| ≤ 8 * R := abs_le.mpr ⟨by linarith, by linarith⟩
  have h4 : |l.2 4| ≤ 8 * R := abs_le.mpr ⟨by linarith, by linarith⟩
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- The assigned chart fits give a bound independent of the chart's small time
and spatial scales. -/
lemma normalizeLine_bound (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ R : ℝ) (hJ : 0 < J) (hδ : 0 < δ) (hR : 0 ≤ R)
    (l : Line)
    (hy : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |y l (t₀ + dt * t) - u - (t₀ + dt * t) * v| ≤ R * J)
    (hx : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |x l (t₀ + dt * t) -
        MvPolynomial.eval ![t₀ + dt * t, y l (t₀ + dt * t)] P| ≤ R * δ) :
    ∀ i, |(normalizeLine P t₀ dt u v J δ l).2 i| ≤ 8 * R := by
  apply coefficients_bound_of_trajectories _ hR
  · intro t ht
    rw [y_normalizeLine, abs_div, abs_of_pos hJ]
    exact (div_le_iff₀ hJ).mpr (hy t ht)
  · intro t ht
    rw [x_normalizeLine P hP, abs_div, abs_of_pos hδ]
    exact (div_le_iff₀ hδ).mpr (hx t ht)

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
