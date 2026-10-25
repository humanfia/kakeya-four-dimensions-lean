/-
Adapted from: here:o107
Written in this tree by x0353.
-/
import Mathlib

/-! Quantitative interpolation at three separated horizontal velocities. -/

namespace Submission.Lib.K4HorizontalCoercivity

theorem separated_product_bound (K E u v x y d : ℝ) (hK : 1 ≤ K)
    (hsep : K⁻¹ ≤ |u - v|) (hx : |x| ≤ E) (hy : |y| ≤ E)
    (hid : (u - v) * d = x - y) : |d| ≤ 2 * K * E := by
  have hK0 : 0 < K := by linarith
  have hs : 1 ≤ K * |u - v| := by
    have hh := mul_le_mul_of_nonneg_left hsep hK0.le
    simpa only [mul_inv_cancel₀ hK0.ne'] using hh
  have hp : |u - v| * |d| ≤ 2 * E := by
    rw [← abs_mul, hid]
    exact (abs_sub x y).trans (by linarith)
  calc
    _ ≤ (K * |u - v|) * |d| := by nlinarith [abs_nonneg d]
    _ = K * (|u - v| * |d|) := by ring
    _ ≤ K * (2 * E) := mul_le_mul_of_nonneg_left hp hK0.le
    _ = _ := by ring

/-- A bounded quadratic at three K-bounded, K-inverse-separated velocities
has all its coefficients bounded with a fixed polynomial loss. -/
theorem horizontal_quadratic_interpolation (a b c K E : ℝ) (hK : 1 ≤ K) (hE : 0 ≤ E)
    (v : Fin 3 → ℝ) (hv : ∀ i, |v i| ≤ K)
    (hsep : ∀ i j, i ≠ j → K⁻¹ ≤ |v i - v j|)
    (hval : ∀ i, |a + b * v i + c * (v i) ^ 2| ≤ E) :
    |a| + |b| + |c| ≤ 32 * K ^ 4 * E := by
  let q : ℝ → ℝ := fun t => a + b * t + c * t ^ 2
  have hs1 : |b + c * (v 1 + v 0)| ≤ 2 * K * E :=
    separated_product_bound K E (v 1) (v 0) (q (v 1)) (q (v 0))
      (b + c * (v 1 + v 0)) hK (hsep 1 0 (by decide)) (hval 1) (hval 0) (by dsimp [q]; ring)
  have hs2 : |b + c * (v 2 + v 0)| ≤ 2 * K * E :=
    separated_product_bound K E (v 2) (v 0) (q (v 2)) (q (v 0))
      (b + c * (v 2 + v 0)) hK (hsep 2 0 (by decide)) (hval 2) (hval 0) (by dsimp [q]; ring)
  have hc : |c| ≤ 4 * K ^ 2 * E := by
    have hh := separated_product_bound K (2 * K * E) (v 1) (v 2)
      (b + c * (v 1 + v 0)) (b + c * (v 2 + v 0)) c hK
      (hsep 1 2 (by decide)) hs1 hs2 (by ring)
    convert hh using 1 <;> ring
  have hK0 : 0 ≤ K := by linarith
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hK3 : K ≤ K ^ 3 := by nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hK2)]
  have hKE : K * E ≤ K ^ 3 * E := mul_le_mul_of_nonneg_right hK3 hE
  have hb : |b| ≤ 10 * K ^ 3 * E := by
    calc
      _ = |(b + c * (v 1 + v 0)) - c * (v 1 + v 0)| := by congr 1; ring
      _ ≤ |b + c * (v 1 + v 0)| + |c * (v 1 + v 0)| := abs_sub _ _
      _ ≤ 2 * K * E + (4 * K ^ 2 * E) * (2 * K) := by
        rw [abs_mul]
        apply add_le_add hs1
        exact mul_le_mul hc ((abs_add_le _ _).trans (by linarith [hv 1, hv 0]))
          (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith
  have hK4 : 1 ≤ K ^ 4 := by nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK2)]
  have ha : |a| ≤ 15 * K ^ 4 * E := by
    calc
      _ = |q (v 0) - b * v 0 - c * (v 0) ^ 2| := by dsimp [q]; congr 1; ring
      _ ≤ |q (v 0) - b * v 0| + |c * (v 0) ^ 2| := abs_sub _ _
      _ ≤ |q (v 0)| + |b * v 0| + |c * (v 0) ^ 2| := by gcongr; exact abs_sub _ _
      _ ≤ E + (10 * K ^ 3 * E) * K + (4 * K ^ 2 * E) * K ^ 2 := by
        simp only [abs_mul, abs_pow]
        have hv02 : |v 0| ^ 2 ≤ K ^ 2 := by nlinarith [hv 0, abs_nonneg (v 0)]
        exact add_le_add
          (add_le_add (hval 0) (mul_le_mul hb (hv 0) (abs_nonneg _) (by positivity)))
          (mul_le_mul hc hv02 (sq_nonneg _) (by positivity))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hK4 hE]
  have hK24 : K ^ 2 ≤ K ^ 4 := by nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK2)]
  have hK34 : K ^ 3 ≤ K ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg hK0 3) (sub_nonneg.mpr hK)]
  nlinarith [mul_le_mul_of_nonneg_right hK24 hE,
    mul_le_mul_of_nonneg_right hK34 hE, mul_nonneg (pow_nonneg hK0 4) hE]

end Submission.Lib.K4HorizontalCoercivity
