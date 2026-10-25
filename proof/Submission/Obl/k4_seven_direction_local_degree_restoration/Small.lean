import Submission.Obl.k4_seven_direction_local_degree_restoration.GraphTaylor

namespace Submission.Obl.k4_seven_direction_local_degree_restoration

/-- The small-nonaffineness case of local degree restoration. The output holds throughout the
entire thickened graph, so the restrictions involving the old polynomial are unnecessary here. -/
theorem small_nonaffine_case (K : ℕ) {A Z b h s : ℝ} {f : Base → ℝ}
    (hA : 2 ≤ A) (hAZ : A ≤ Z) (hb : 0 < b)
    (hf : ContDiffOn ℝ 6 f (Metric.ball (0 : Base) 3))
    (h0 : |f 0| ≤ Z) (h1 : ‖fderiv ℝ f 0‖ ≤ Z)
    (h2 : ‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z)
    (hthird : ∀ u ∈ Metric.closedBall (0 : Base) 2,
      ‖iteratedFDeriv ℝ 3 f u‖ ≤ A ^ K * (b + s * h)) (hsmall : s * h ≤ b) :
    ∃ Q : Poly, Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ Z ^ (K + 5)) ∧
      ∀ u ∈ Metric.closedBall (0 : Base) 1, ∀ w : ℝ, |w - f u| ≤ A * b →
      |MvPolynomial.eval ![u 0, u 1, u 2, w] Q| ≤ A ^ (K + 5) * b ∧
      A ^ (-((K + 5 : ℕ) : ℤ)) ≤
        |MvPolynomial.eval ![u 0, u 1, u 2, w] (MvPolynomial.pderiv (3 : Fin 4) Q)| ∧
      |MvPolynomial.eval ![u 0, u 1, u 2, w] (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ A ^ (K + 5) ∧
      |MvPolynomial.eval ![u 0, u 1, u 2, w]
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤
          A ^ (K + 5) / b := by
  have hA0 : 0 ≤ A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hthird' : ∀ u ∈ Metric.closedBall (0 : Base) 1,
      ‖iteratedFDeriv ℝ 3 f u‖ ≤ 2 * A ^ K * b := by
    intro u hu
    refine (hthird u (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hu)).trans ?_
    calc A ^ K * (b + s * h) ≤ A ^ K * (2 * b) :=
           mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hA0 K)
         _ = 2 * A ^ K * b := by ring
  obtain ⟨hdeg, hcoeff, hdw, hval⟩ := quadraticTaylorGraph_bounds
    (hf.of_le (by norm_num)) (by linarith : 2 ≤ Z) h0 h1 h2 hthird' (d := A * b)
  refine ⟨quadraticTaylorGraph f, hdeg, ?_, ?_⟩
  · intro e
    exact (hcoeff e).trans (pow_le_pow_right₀ hZ1 (by omega : 5 ≤ K + 5))
  · intro u hu w hw
    have hAK : 0 ≤ A ^ K := pow_nonneg hA0 K
    have hAK1 : 0 ≤ A ^ (K + 1) := pow_nonneg hA0 _
    have hmono : A + A ^ K ≤ A ^ (K + 2) := by
      calc A + A ^ K ≤ A ^ (K + 1) + A ^ (K + 1) :=
             add_le_add (by simpa using pow_le_pow_right₀ hA1 (by omega : 1 ≤ K + 1))
               (pow_le_pow_right₀ hA1 (by omega : K ≤ K + 1))
           _ = 2 * A ^ (K + 1) := by ring
           _ ≤ A * A ^ (K + 1) := mul_le_mul_of_nonneg_right hA hAK1
           _ = A ^ (K + 2) := by ring
    have hv : A * b + (2 * A ^ K * b) / 6 ≤ A ^ (K + 5) * b := by
      calc A * b + (2 * A ^ K * b) / 6 ≤ (A + A ^ K) * b := by
             nlinarith [mul_nonneg hAK hb.le]
           _ ≤ A ^ (K + 2) * b := mul_le_mul_of_nonneg_right hmono hb.le
           _ ≤ A ^ (K + 5) * b := mul_le_mul_of_nonneg_right
             (pow_le_pow_right₀ hA1 (by omega : K + 2 ≤ K + 5)) hb.le
    refine ⟨(hval u hu w hw).trans hv, ?_⟩
    rw [hdw]
    simp only [map_one, abs_one, MvPolynomial.pderiv_one, map_zero, abs_zero]
    refine ⟨?_, one_le_pow₀ hA1, by positivity⟩
    rw [zpow_neg, zpow_natCast]
    exact (inv_le_one₀ (pow_pos (by linarith : 0 < A) _)).2 (one_le_pow₀ hA1)

end Submission.Obl.k4_seven_direction_local_degree_restoration
