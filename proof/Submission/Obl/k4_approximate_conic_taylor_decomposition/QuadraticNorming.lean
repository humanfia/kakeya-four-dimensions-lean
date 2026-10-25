/- Adapted from this LOT tree, o144, session x0488, commit 5ed40f2, Submission/Obl/k4_seven_direction_local_degree_restoration/QuadraticNorming.lean. -/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Forms
import Submission.Obl.k4_real_conic_restoration.Shift

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

open Submission.Obl.k4_real_conic_restoration (quad coeff coeff_le coeff_nonneg quad_shift)

lemma quadratic_coeff_le_of_ball_bound {Q : Matrix (Fin 3) (Fin 3) ℝ} (hQ : Q.IsSymm)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ u ∈ Metric.closedBall (0 : E3) 2, |quad Q (fun i => u i)| ≤ B) :
    coeff Q ≤ 18 * B := by
  let e : Fin 3 → E3 := fun i => EuclideanSpace.basisFun (Fin 3) ℝ i
  have he (i : Fin 3) : ‖e i‖ = 1 := by simp [e, EuclideanSpace.basisFun_apply]
  have hdiag (i : Fin 3) : |Q i i| ≤ B := by
    have ht := hbound (e i) (by simp [he i])
    simpa [e, EuclideanSpace.basisFun_apply, quad, PiLp.single_apply] using ht
  have hpair (i j : Fin 3) : |Q i i + 2 * Q i j + Q j j| ≤ B := by
    have hnorm : ‖e i + e j‖ ≤ 2 := (norm_add_le _ _).trans (by rw [he i, he j]; norm_num)
    have ht := hbound (e i + e j) (by simpa using hnorm)
    have hshift := quad_shift hQ (Pi.single i 1) j 1
    have heq : (fun k => (e i + e j) k) = Pi.single i 1 + Pi.single j 1 := by
      funext k
      simp [e, EuclideanSpace.basisFun_apply, PiLp.single_apply, Pi.single_apply]
    rw [heq, hshift] at ht
    simpa [quad, Matrix.vecMul, dotProduct, Pi.single_apply] using ht
  apply (coeff_le (B := 2 * B) ?_).trans_eq (by ring)
  intro i j
  have htriangle : |2 * Q i j| ≤ |Q i i + 2 * Q i j + Q j j| + |Q i i| + |Q j j| := by
    have h1 := abs_sub (Q i i + 2 * Q i j + Q j j) (Q i i)
    have h2 := abs_sub ((Q i i + 2 * Q i j + Q j j) - Q i i) (Q j j)
    have heq : ((Q i i + 2 * Q i j + Q j j) - Q i i) - Q j j = 2 * Q i j := by ring
    rw [heq] at h2
    linarith
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htriangle
  linarith [hpair i j, hdiag i, hdiag j]

/-- A symmetric quadratic is normed by one point of the radius-two ball. -/
lemma exists_quadratic_norming_point (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm) :
    ∃ u ∈ Metric.closedBall (0 : E3) 2,
      coeff Q ≤ 18 * |quad Q (fun i => u i)| := by
  have hcont : Continuous (fun u : E3 => |quad Q (fun i => u i)|) := by
    unfold quad
    fun_prop
  obtain ⟨u, hu, hmax⟩ := (isCompact_closedBall (0 : E3) 2).exists_isMaxOn
    (show (Metric.closedBall (0 : E3) 2).Nonempty from ⟨0, by simp⟩) hcont.continuousOn
  exact ⟨u, hu, quadratic_coeff_le_of_ball_bound hQ (abs_nonneg _) (fun v hv => hmax hv)⟩

/-- Dividing a bounded scalar multiple of the square of a nonzero quadratic costs only the square
of its coefficient lower bound. -/
lemma abs_scalar_le_of_quadratic_square_bound {Q : Matrix (Fin 3) (Fin 3) ℝ}
    (hQ : Q.IsSymm) {c M lam : ℝ} (hc : 0 < c) (_hM : 0 ≤ M) (hlower : c ≤ coeff Q)
    (hbound : ∀ u ∈ Metric.closedBall (0 : E3) 2, |lam * (quad Q (fun i => u i)) ^ 2| ≤ M) :
    |lam| ≤ 324 * M / c ^ 2 := by
  obtain ⟨u, hu, hnorm⟩ := exists_quadratic_norming_point Q hQ
  have hq : c ≤ 18 * |quad Q (fun i => u i)| := hlower.trans hnorm
  have hq2 : c ^ 2 ≤ 324 * (quad Q (fun i => u i)) ^ 2 := by
    have := pow_le_pow_left₀ hc.le hq 2
    norm_num [mul_pow, sq_abs] at this
    exact this
  have hb := hbound u hu
  rw [abs_mul, abs_pow, sq_abs] at hb
  apply (le_div_iff₀ (sq_pos_of_pos hc)).2
  have hprod := mul_le_mul_of_nonneg_left hq2 (abs_nonneg lam)
  nlinarith only [hprod, hb]

lemma abs_scalar_le_power_of_quadratic_square_bound (J : ℕ)
    {Q : Matrix (Fin 3) (Fin 3) ℝ} (hQ : Q.IsSymm) {A lam : ℝ} (hA : 2 ≤ A)
    (hlower : (A ^ 4)⁻¹ ≤ coeff Q)
    (hbound : ∀ u ∈ Metric.closedBall (0 : E3) 2,
      |lam * (quad Q (fun i => u i)) ^ 2| ≤ A ^ J) :
    |lam| ≤ A ^ (J + 17) := by
  have hA0 : 0 < A := by linarith
  have h324 : (324 : ℝ) ≤ A ^ 9 := by
    calc (324 : ℝ) ≤ 2 ^ 9 := by norm_num
         _ ≤ A ^ 9 := pow_le_pow_left₀ (by norm_num) hA 9
  have ht := abs_scalar_le_of_quadratic_square_bound hQ
    (inv_pos.mpr (pow_pos hA0 4)) (pow_nonneg hA0.le J) hlower hbound
  refine ht.trans ?_
  calc 324 * A ^ J / ((A ^ 4)⁻¹) ^ 2 = 324 * A ^ (J + 8) := by
         simp only [div_eq_mul_inv, inv_pow, inv_inv, pow_add]
         ring
       _ ≤ A ^ 9 * A ^ (J + 8) := mul_le_mul_of_nonneg_right h324 (pow_nonneg hA0.le _)
       _ = A ^ (J + 17) := by rw [← pow_add]; congr 1; omega

end Submission.Obl.k4_approximate_conic_taylor_decomposition
