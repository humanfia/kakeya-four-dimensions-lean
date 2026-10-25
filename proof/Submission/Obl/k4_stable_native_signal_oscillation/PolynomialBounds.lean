import Submission.Obl.k4_stable_native_signal_oscillation.Coefficients

namespace Submission.Obl.k4_stable_native_signal_oscillation
open Set MvPolynomial Metric

lemma exists_polynomial_lipschitz_degree (D : ℕ) : ∃ L : ℝ, 0 < L ∧
    ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
    ∀ A : ℝ, 0 ≤ A → (∀ m, |P.coeff m| ≤ A) →
    ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |eval (fun i => x i) P - eval (fun i => y i) P| ≤ L * A * ‖x - y‖ := by
  classical
  let m (d : Fin 3 → Fin (D + 1)) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
    ∏ i, x i ^ (d i : ℕ)
  have hK : ∀ d, ∃ K : NNReal, LipschitzOnWith K (m d)
      (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    intro d
    have hd : ContDiff ℝ 1 (m d) := by dsimp [m]; fun_prop
    exact hd.contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall _ _) (isCompact_closedBall _ _)
  choose K hK using hK
  let L : ℝ := (∑ d, (K d : ℝ)) + 1
  have hsum : 0 ≤ ∑ d, (K d : ℝ) := Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)
  refine ⟨L, by dsimp [L]; linarith, ?_⟩
  intro P hP A hA hcoeff x y hx hy
  have heval (u : EuclideanSpace ℝ (Fin 3)) :
      eval (fun i => u i) P = ∑ d, P.coeff (boxExponent d) * m d u := by
    conv_lhs => rw [← boxPolynomial_coefficients P hP]
    simp only [boxPolynomial, eval_sum, eval_monomial]
    apply Finset.sum_congr rfl
    intro d hd
    congr 1
    rw [Finsupp.prod_fintype]
    · simp [m, boxExponent]
    · intro i; simp
  rw [heval, heval, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d, |P.coeff (boxExponent d) * m d x - P.coeff (boxExponent d) * m d y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d, A * (K d : ℝ) * ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← mul_sub, abs_mul]
      have hmono : |m d x - m d y| ≤ (K d : ℝ) * ‖x - y‖ := by
        simpa only [dist_eq_norm, Real.norm_eq_abs] using
          (hK d).dist_le_mul x (by simpa using hx) y (by simpa using hy)
      exact (mul_le_mul (hcoeff _) hmono (abs_nonneg _) hA).trans_eq (by ring)
    _ = (∑ d, (K d : ℝ)) * A * ‖x - y‖ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ L * A * ‖x - y‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hA
      dsimp [L]
      linarith

lemma exists_polynomial_lipschitz_of_ball_bound (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
    ∀ V : ℝ, 0 ≤ V →
    (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 8 → |eval (fun i => x i) P| ≤ V) →
    ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |eval (fun i => x i) P - eval (fun i => y i) P| ≤ C * V * ‖x - y‖ := by
  obtain ⟨C, hC, hcoeff⟩ := exists_coefficient_bound_on_ball_degree D
  obtain ⟨L, hL, hlip⟩ := exists_polynomial_lipschitz_degree D
  refine ⟨L * C, mul_pos hL hC, ?_⟩
  intro P hP V hV hbound x y hx hy
  exact (hlip P hP (C * V) (mul_nonneg hC.le hV) (hcoeff P hP V hV hbound) x y hx hy).trans_eq
    (by ring)

end Submission.Obl.k4_stable_native_signal_oscillation
