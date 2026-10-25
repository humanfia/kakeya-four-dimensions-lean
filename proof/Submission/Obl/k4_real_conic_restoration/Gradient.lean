import Submission.Obl.k4_real_conic_restoration.Coordinates

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Submission.Obl.k4_real_conic_restoration

theorem quad_euler (Q : Mat) (p : Vec) :
    quad Q p = p 0 * Matrix.vecMul p Q 0 + p 1 * Matrix.vecMul p Q 1 +
      p 2 * Matrix.vecMul p Q 2 := by
  simp only [quad, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  ring

theorem det_le_affine_gradient {Q : Mat} {p : Vec} {A ε : ℝ}
    (hA : 1 ≤ A) (hε : 0 ≤ ε) (hp0 : p 0 = 1)
    (hp : ∀ j, |p j| ≤ A) (hQ : ∀ i j, |Q i j| ≤ A) (hq : |quad Q p| ≤ ε) :
    |Q.det| ≤ 2 * A ^ 2 * ε +
      4 * A ^ 3 * (|Matrix.vecMul p Q 1| + |Matrix.vecMul p Q 2|) := by
  have hA0 : 0 ≤ A := by linarith
  let g := Matrix.vecMul p Q
  have hid : Matrix.vecMul g Q.adjugate 0 = Q.det := by
    dsimp [g]
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    simp [hp0]
  have hdet : |Q.det| ≤ 2 * A ^ 2 * (|g 0| + |g 1| + |g 2|) := by
    rw [← hid]
    calc
      _ ≤ ∑ i, |g i * Q.adjugate i 0| := abs_sum_le _
      _ ≤ ∑ i, |g i| * (2 * A ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (adjugate_bound hQ i 0) (abs_nonneg _)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  have heq : g 0 = quad Q p - p 1 * g 1 - p 2 * g 2 := by
    have h := quad_euler Q p
    rw [hp0] at h
    dsimp [g]
    linarith
  have hg0 : |g 0| ≤ ε + A * (|g 1| + |g 2|) := by
    rw [heq]
    calc
      _ ≤ |quad Q p - p 1 * g 1| + |p 2 * g 2| := abs_sub _ _
      _ ≤ (|quad Q p| + |p 1 * g 1|) + |p 2 * g 2| := by gcongr; exact abs_sub _ _
      _ ≤ (ε + A * |g 1|) + A * |g 2| := by
        simp only [abs_mul]
        gcongr
        exact hp 1
        exact hp 2
      _ = _ := by ring
  calc
    |Q.det| ≤ 2 * A ^ 2 * (ε + A * (|g 1| + |g 2|) + |g 1| + |g 2|) := by
      exact hdet.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    _ ≤ 2 * A ^ 2 * ε + 4 * A ^ 3 * (|g 1| + |g 2|) := by
      nlinarith [mul_nonneg (show 0 ≤ 2 * A ^ 2 by positivity)
        (mul_nonneg (show 0 ≤ A - 1 by linarith) (show 0 ≤ |g 1| + |g 2| by positivity))]

theorem affine_gradient_lower {Q : Mat} {p : Vec} {A ε : ℝ}
    (hA : 2 ≤ A) (hε : 0 ≤ ε) (hs : ε * A ^ 1000 ≤ 1)
    (hp0 : p 0 = 1) (hp : ∀ j, |p j| ≤ A) (hQ : ∀ i j, |Q i j| ≤ A)
    (hq : |quad Q p| ≤ ε) (hd : 1 ≤ A ^ 760 * |Q.det|) :
    ∃ j : Fin 3, j ≠ 0 ∧ 1 ≤ A ^ 770 * |Matrix.vecMul p Q j| := by
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  by_contra hn
  have h1 : A ^ 770 * |Matrix.vecMul p Q 1| < 1 := by
    exact lt_of_not_ge (fun h => hn ⟨1, by decide, h⟩)
  have h2 : A ^ 770 * |Matrix.vecMul p Q 2| < 1 := by
    exact lt_of_not_ge (fun h => hn ⟨2, by decide, h⟩)
  have he := small_power hA1 hε hs (by decide : 769 ≤ 1000)
  have hgrad := det_le_affine_gradient hA1 hε hp0 hp hQ hq
  have hh : A ^ 7 ≤ 2 * (ε * A ^ 769) +
      4 * (A ^ 770 * |Matrix.vecMul p Q 1| + A ^ 770 * |Matrix.vecMul p Q 2|) := by
    calc
      A ^ 7 ≤ A ^ 7 * (A ^ 760 * |Q.det|) := le_mul_of_one_le_right (by positivity) hd
      _ ≤ A ^ 7 * (A ^ 760 * (2 * A ^ 2 * ε +
        4 * A ^ 3 * (|Matrix.vecMul p Q 1| + |Matrix.vecMul p Q 2|))) := by gcongr
      _ = _ := by ring
  have hAp : (2 : ℝ) ^ 7 ≤ A ^ 7 := pow_le_pow_left₀ (by norm_num) hA 7
  norm_num at hAp
  linarith

end Submission.Obl.k4_real_conic_restoration
