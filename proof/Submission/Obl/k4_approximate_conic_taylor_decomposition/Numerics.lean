import Mathlib

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

/-- A stronger scale hypothesis absorbs any smaller power of the conditioning parameter. -/
lemma scale_error_mono {A ε h : ℝ} {m K : ℕ} (hA : 1 ≤ A) (hh : 0 ≤ h)
    (hm : m ≤ K) (hscale : h * A ^ K ≤ ε) : A ^ m * h ≤ ε := by
  calc
    A ^ m * h ≤ A ^ K * h := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hm) hh
    _ ≤ ε := by simpa only [mul_comm] using hscale

/-- A common error budget covers all three restored polynomial tests. -/
lemma restored_test_error_le (D K : ℕ) {A ε h : ℝ} (hA : 2 ≤ A)
    (hε : 0 ≤ ε) (hh : 0 ≤ h) (hK : 4 * D + 22 ≤ K) (hscale : h * A ^ K ≤ ε) :
    20 * A * ε + 1620 * (A ^ 6) ^ 2 * A ^ 9 * (A ^ (4 * D + 1) * h) ≤ A ^ 12 * ε := by
  have hA0 : 0 ≤ A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hsmall := scale_error_mono hA1 hh hK hscale
  have h20 : (20 : ℝ) ≤ A ^ 5 :=
    (show (20 : ℝ) ≤ 2 ^ 5 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hA 5)
  have h1620 : (1620 : ℝ) ≤ A ^ 11 :=
    (show (1620 : ℝ) ≤ 2 ^ 11 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hA 11)
  have htwentyA : 20 * A ≤ A ^ 11 := by
    calc
      20 * A ≤ A ^ 5 * A := mul_le_mul_of_nonneg_right h20 hA0
      _ = A ^ 6 := by ring
      _ ≤ A ^ 11 := pow_le_pow_right₀ hA1 (by norm_num)
  calc
    _ = 20 * A * ε + 1620 * (A ^ (4 * D + 22) * h) := by ring
    _ ≤ (20 * A + 1620) * ε := by nlinarith only [hsmall]
    _ ≤ (A ^ 11 + A ^ 11) * ε := mul_le_mul_of_nonneg_right (add_le_add htwentyA h1620) hε
    _ ≤ (A * A ^ 11) * ε := mul_le_mul_of_nonneg_right (by
      nlinarith only [hA, pow_nonneg hA0 11]) hε
    _ = A ^ 12 * ε := by ring

/-- One fixed coefficient exponent covers all three exact-conic kernels after restoration. -/
lemma restored_kernel_error_le (D : ℕ) {A ε : ℝ} (hA : 2 ≤ A) (hε : 0 ≤ ε) :
    (A ^ 6) ^ (137 + 16 * (4 * D)) * (A ^ 12 * ε) ≤ A ^ (900 + 400 * D) * ε := by
  have hA1 : 1 ≤ A := by linarith
  calc
    _ = A ^ (834 + 384 * D) * ε := by ring
    _ ≤ A ^ (900 + 400 * D) * ε := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hA1 (by omega)) hε

end Submission.Obl.k4_approximate_conic_taylor_decomposition
