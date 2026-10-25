import Submission.Obl.k4_real_conic_restoration.Gradient
import Submission.Obl.k4_real_conic_restoration.ScalarRoot

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Submission.Obl.k4_real_conic_restoration

/-- Restriction of a symmetric quadratic to a coordinate line. -/
theorem quad_shift {Q : Mat} (hQ : Q.IsSymm) (p : Vec) (j : Fin 3) (t : ℝ) :
    quad Q (p + Pi.single j t) =
      quad Q p + (2 * Matrix.vecMul p Q j) * t + Q j j * t ^ 2 := by
  fin_cases j <;>
    simp [quad, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      hQ.apply 0 1, hQ.apply 0 2, hQ.apply 1 2] <;> ring

set_option maxHeartbeats 1000000 in
/-- Correct an affine point by moving in one spatial coordinate. -/
theorem restore_point {Q : Mat} {p : EuclideanSpace ℝ (Fin 3)} {A ε : ℝ}
    (hA : 2 ≤ A) (hε : 0 ≤ ε) (hs : ε * A ^ 10000 ≤ 1)
    (hp0 : p 0 = 1) (hp : ∀ j, |p j| ≤ A) (hQ : Q.IsSymm)
    (hQu : ∀ i j, |Q i j| ≤ A) (hq : |quad Q p| ≤ ε)
    (hd : 1 ≤ A ^ 760 * |Q.det|) :
    ∃ p' : EuclideanSpace ℝ (Fin 3),
      p' 0 = 1 ∧ quad Q p' = 0 ∧ ‖p' - p‖ ≤ A ^ 771 * ε := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hs1000 := small_power hA1 hε hs (by decide : 1000 ≤ 10000)
  obtain ⟨j, hj, hgj⟩ := affine_gradient_lower hA hε hs1000 hp0 hp hQu hq hd
  let b : ℝ := 2 * Matrix.vecMul p Q j
  have hbsize : 1 ≤ A ^ 770 * |b| := by
    dsimp [b]
    rw [abs_mul]
    norm_num
    nlinarith [abs_nonneg (Matrix.vecMul p Q j), show 0 ≤ A ^ 770 by positivity]
  have hb : b ≠ 0 := by
    intro he
    rw [he, abs_zero, mul_zero] at hbsize
    norm_num at hbsize
  have hbinv : |b|⁻¹ ≤ A ^ 770 :=
    (inv_le_iff_one_le_mul₀ (abs_pos.mpr hb)).mpr hbsize
  have hbsq : 1 ≤ b ^ 2 * A ^ 1540 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hbsize 2
    calc
      1 ≤ (A ^ 770 * |b|) ^ 2 := by simpa only [one_pow] using hh
      _ = b ^ 2 * A ^ 1540 := by rw [mul_pow, sq_abs]; ring
  have hbA2 : (4 : ℝ) ≤ A ^ 2 := by
    exact (show (4 : ℝ) = 2 ^ 2 by norm_num).le.trans (pow_le_pow_left₀ (by norm_num) hA 2)
  have hsmallscaled : (4 * |Q j j| * |quad Q p|) * A ^ 1540 ≤ 1 := by
    calc
      _ ≤ (4 * A * ε) * A ^ 1540 := by gcongr; exact hQu j j
      _ = 4 * ε * A ^ 1541 := by ring
      _ ≤ A ^ 2 * ε * A ^ 1541 := by gcongr
      _ = ε * A ^ 1543 := by ring
      _ ≤ 1 := small_power hA1 hε hs (by decide : 1543 ≤ 10000)
  have hsmall : 4 * |Q j j| * |quad Q p| ≤ b ^ 2 := by
    exact (mul_le_mul_iff_left₀ (pow_pos hA0 1540)).mp (hsmallscaled.trans hbsq)
  obtain ⟨t, ht, htb⟩ := quadratic_near_zero (Q j j) b (quad Q p) hb hsmall
  let p' := p + EuclideanSpace.single j t
  refine ⟨p', ?_, ?_, ?_⟩
  · simp [p', PiLp.single_apply, hj.symm, hp0]
  · change quad Q ((fun i => p i) + Pi.single j t) = 0
    rw [quad_shift hQ]
    exact ht
  · have hn : ‖p' - p‖ = |t| := by
      simp [p', PiLp.norm_single, Real.norm_eq_abs]
    rw [hn]
    calc
      |t| ≤ 2 * |quad Q p| / |b| := htb
      _ ≤ 2 * ε * A ^ 770 := by
        rw [div_eq_mul_inv]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num)) hbinv
          (inv_nonneg.mpr (abs_nonneg b)) (by positivity)
      _ ≤ A ^ 771 * ε := by
        calc
          _ ≤ A * ε * A ^ 770 := by gcongr
          _ = _ := by ring

end Submission.Obl.k4_real_conic_restoration
