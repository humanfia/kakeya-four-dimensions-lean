import Submission.Lib.K4ChartLifting.Normalize

/-!
# Size bounds for lifted charts

Planar norms of matrix images, and `ℓ¹` bounds for the substitution polynomials
and lifted tests.
-/

namespace Submission.Lib.K4ChartLifting

open MvPolynomial

theorem plane_abs_le_norm (v : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  simpa [Real.norm_eq_abs] using this

theorem plane_norm_le (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ≤ |v 0| + |v 1| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), sq_abs (v 0), sq_abs (v 1),
    mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1))]

theorem toEuclideanLin_apply_two (A : Matrix (Fin 2) (Fin 2) ℝ) (v : EuclideanSpace ℝ (Fin 2))
    (e : Fin 2) : (Matrix.toEuclideanLin A v) e = A e 0 * v 0 + A e 1 * v 1 := by
  fin_cases e <;> simp [Matrix.toLpLin_apply]

theorem norm_toEuclideanLin_le (A : Matrix (Fin 2) (Fin 2) ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖Matrix.toEuclideanLin A v‖ ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |A e e'|) * ‖v‖ := by
  refine (plane_norm_le _).trans ?_
  rw [toEuclideanLin_apply_two, toEuclideanLin_apply_two]
  have k : ∀ a b : ℝ, |a * v 0 + b * v 1| ≤ (|a| + |b|) * ‖v‖ := by
    intro a b
    have h0 := plane_abs_le_norm v 0
    have h1 := plane_abs_le_norm v 1
    calc |a * v 0 + b * v 1| ≤ |a| * |v 0| + |b| * |v 1| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| * ‖v‖ + |b| * ‖v‖ := by gcongr
      _ = (|a| + |b|) * ‖v‖ := by ring
  have := k (A 0 0) (A 0 1)
  have := k (A 1 0) (A 1 1)
  simp only [Fin.sum_univ_two]
  linarith

namespace Frame
variable (F : Frame)

/-- A bound for the `ℓ¹` norms of the substitution polynomials. -/
noncomputable def substBound : ℝ :=
  1 + |F.q⁻¹| * (1 + |F.t₀|) + (∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'|) * (1 + ‖F.c‖ + ‖F.u‖)

theorem one_le_substBound : 1 ≤ F.substBound := by
  have h1 : 0 ≤ |F.q⁻¹| * (1 + |F.t₀|) := by positivity
  have h2 : 0 ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'|) * (1 + ‖F.c‖ + ‖F.u‖) := by
    positivity
  unfold substBound; linarith

theorem coeffL1_row_le (a b : ℝ) (j₁ j₂ : Fin 4) (c₁ c₂ u₁ u₂ : ℝ) :
    coeffL1 (C a * (X j₁ - C c₁ - X 0 * C u₁) + C b * (X j₂ - C c₂ - X 0 * C u₂) :
      MvPolynomial (Fin 4) ℝ) ≤ |a| * (1 + |c₁| + |u₁|) + |b| * (1 + |c₂| + |u₂|) := by
  have k : ∀ (j : Fin 4) (c u : ℝ),
      coeffL1 (X j - C c - X 0 * C u : MvPolynomial (Fin 4) ℝ) ≤ 1 + |c| + |u| := by
    intro j c u
    calc coeffL1 (X j - C c - X 0 * C u : MvPolynomial (Fin 4) ℝ)
        ≤ coeffL1 (X j - C c : MvPolynomial (Fin 4) ℝ) + coeffL1 (X 0 * C u) :=
          coeffL1_sub_le _ _
      _ ≤ (coeffL1 (X j : MvPolynomial (Fin 4) ℝ) + coeffL1 (C c : MvPolynomial (Fin 4) ℝ)) +
          coeffL1 (X 0 : MvPolynomial (Fin 4) ℝ) * |u| :=
          add_le_add (coeffL1_sub_le _ _) (coeffL1_mul_C_le _ _)
      _ = 1 + |c| + |u| := by rw [coeffL1_X, coeffL1_C, coeffL1_X]; ring
  calc _ ≤ coeffL1 (C a * (X j₁ - C c₁ - X 0 * C u₁) : MvPolynomial (Fin 4) ℝ) +
        coeffL1 (C b * (X j₂ - C c₂ - X 0 * C u₂) : MvPolynomial (Fin 4) ℝ) := coeffL1_add_le _ _
    _ ≤ |a| * (1 + |c₁| + |u₁|) + |b| * (1 + |c₂| + |u₂|) := by
      apply add_le_add
      · exact (coeffL1_C_mul_le _ _).trans (mul_le_mul_of_nonneg_left (k _ _ _) (abs_nonneg _))
      · exact (coeffL1_C_mul_le _ _).trans (mul_le_mul_of_nonneg_left (k _ _ _) (abs_nonneg _))

theorem coeffL1_subst_le (i : Fin 4) : coeffL1 (F.subst i) ≤ F.substBound := by
  have hS := F.one_le_substBound
  have hc0 := plane_abs_le_norm F.c 0
  have hc1 := plane_abs_le_norm F.c 1
  have hu0 := plane_abs_le_norm F.u 0
  have hu1 := plane_abs_le_norm F.u 1
  have hD : ∀ e e', |F.D⁻¹ e e'| ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'| := by
    intro e e'
    calc |F.D⁻¹ e e'| ≤ ∑ e' : Fin 2, |F.D⁻¹ e e'| :=
          Finset.single_le_sum (f := fun e' => |F.D⁻¹ e e'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ e')
      _ ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'| :=
          Finset.single_le_sum (f := fun e => ∑ e' : Fin 2, |F.D⁻¹ e e'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ e)
  have hsum : ∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'| =
      |F.D⁻¹ 0 0| + |F.D⁻¹ 0 1| + (|F.D⁻¹ 1 0| + |F.D⁻¹ 1 1|) := by
    simp [Fin.sum_univ_two]
  have hnn : 0 ≤ ‖F.c‖ + ‖F.u‖ := by positivity
  have hrow : ∀ a b : ℝ, |a| * (1 + |F.c 0| + |F.u 0|) + |b| * (1 + |F.c 1| + |F.u 1|) ≤
      (|a| + |b|) * (1 + ‖F.c‖ + ‖F.u‖) := by
    intro a b
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    nlinarith
  have hP : 0 ≤ |F.q⁻¹| * (1 + |F.t₀|) := by positivity
  have hQ : 0 ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'|) * (1 + ‖F.c‖ + ‖F.u‖) := by positivity
  fin_cases i
  · show coeffL1 (C F.q⁻¹ * (X 0 - C F.t₀)) ≤ F.substBound
    calc coeffL1 (C F.q⁻¹ * (X 0 - C F.t₀) : MvPolynomial (Fin 4) ℝ)
        ≤ |F.q⁻¹| * coeffL1 (X 0 - C F.t₀ : MvPolynomial (Fin 4) ℝ) := coeffL1_C_mul_le _ _
      _ ≤ |F.q⁻¹| * (1 + |F.t₀|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          refine (coeffL1_sub_le _ _).trans ?_
          rw [coeffL1_X, coeffL1_C]
      _ ≤ F.substBound := by unfold substBound; linarith
  · show coeffL1 (C (F.D⁻¹ 0 0) * (X 1 - C (F.c 0) - X 0 * C (F.u 0)) +
      C (F.D⁻¹ 0 1) * (X 2 - C (F.c 1) - X 0 * C (F.u 1))) ≤ F.substBound
    refine (coeffL1_row_le _ _ _ _ _ _ _ _).trans ((hrow _ _).trans ?_)
    unfold substBound
    have : |F.D⁻¹ 0 0| + |F.D⁻¹ 0 1| ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'| := by
      rw [hsum]; have := abs_nonneg (F.D⁻¹ 1 0); have := abs_nonneg (F.D⁻¹ 1 1); linarith
    nlinarith
  · show coeffL1 (C (F.D⁻¹ 1 0) * (X 1 - C (F.c 0) - X 0 * C (F.u 0)) +
      C (F.D⁻¹ 1 1) * (X 2 - C (F.c 1) - X 0 * C (F.u 1))) ≤ F.substBound
    refine (coeffL1_row_le _ _ _ _ _ _ _ _).trans ((hrow _ _).trans ?_)
    unfold substBound
    have : |F.D⁻¹ 1 0| + |F.D⁻¹ 1 1| ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'| := by
      rw [hsum]; have := abs_nonneg (F.D⁻¹ 0 0); have := abs_nonneg (F.D⁻¹ 0 1); linarith
    nlinarith
  · show coeffL1 (X 3 : MvPolynomial (Fin 4) ℝ) ≤ F.substBound
    rw [coeffL1_X]; exact hS

/-- Coefficient bound of a lifted test. -/
theorem abs_coeff_liftTest_le (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) (e : Fin 4 →₀ ℕ) :
    |(F.liftTest δ R).coeff e| ≤ |δ| * (coeffL1 R * F.substBound ^ R.totalDegree) := by
  refine (abs_coeff_le_coeffL1 _ e).trans ?_
  refine (coeffL1_smul _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (coeffL1_bind₁_le _ _ F.one_le_substBound
    F.coeffL1_subst_le R) (abs_nonneg _)

end Frame
end Submission.Lib.K4ChartLifting
