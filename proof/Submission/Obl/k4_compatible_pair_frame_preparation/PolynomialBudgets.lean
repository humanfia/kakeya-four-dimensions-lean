import Mathlib

namespace Submission.Obl.k4_compatible_pair_frame_preparation

/-- Fixed constants in center and velocity bounds cost only five integer powers. -/
theorem center_polynomial_budget {N K : ℝ} (hN : 2 ≤ N) (hK : K ≤ N) (M : ℕ) :
    4 * N ^ M + 8 * K ≤ N ^ (M + 5) := by
  have hN1 : 1 ≤ N := by linarith
  have hM : 1 ≤ N ^ M := one_le_pow₀ hN1
  have h1 : N ^ M ≤ N ^ M * N := le_mul_of_one_le_right (by positivity) hN1
  have h2 : N ≤ N ^ M * N := le_mul_of_one_le_left (by positivity) hM
  have hc : (12 : ℝ) ≤ N ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 4
    norm_num at this
    linarith
  calc
    4 * N ^ M + 8 * K ≤ 12 * (N ^ M * N) := by linarith
    _ ≤ N ^ 4 * (N ^ M * N) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = N ^ (M + 5) := by rw [pow_add]; ring

/-- Fixed constants in matrix and inverse bounds cost four integer powers. -/
theorem matrix_polynomial_budget {N : ℝ} (hN : 2 ≤ N) (M : ℕ) :
    4 * N + 4 * N ^ M ≤ N ^ (M + 4) := by
  have hN1 : 1 ≤ N := by linarith
  have hM : 1 ≤ N ^ M := one_le_pow₀ hN1
  have h1 : N ^ M ≤ N ^ M * N := le_mul_of_one_le_right (by positivity) hN1
  have h2 : N ≤ N ^ M * N := le_mul_of_one_le_left (by positivity) hM
  have hc : (8 : ℝ) ≤ N ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3
    norm_num at this
    linarith
  calc
    4 * N + 4 * N ^ M ≤ 8 * (N ^ M * N) := by linarith
    _ ≤ N ^ 3 * (N ^ M * N) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = N ^ (M + 4) := by rw [pow_add]; ring

/-- The affine substitution scale is polynomial in a common bound on its data. -/
theorem substitution_polynomial_budget {Z K C Q B H : ℝ} (hZ : 2 ≤ Z)
    (hK0 : 0 ≤ K) (hK : K ≤ Z) (hC0 : 0 ≤ C) (hC : C ≤ Z)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ Z) (hB : B ≤ Z)
    (hH : H ≤ 1 + (1 + 100 * K) * (1 + 2 * C) + 2 * C + 100 * K * Q + B) :
    H ≤ Z ^ 11 := by
  have hZ1 : 1 ≤ Z := by linarith
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  have hZsq : 1 ≤ Z ^ 2 := one_le_pow₀ hZ1
  have hc : (407 : ℝ) ≤ Z ^ 9 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hZ 9
    norm_num at this
    linarith
  calc
    H ≤ 1 + (1 + 100 * K) * (1 + 2 * C) + 2 * C + 100 * K * Q + B := hH
    _ ≤ 1 + (101 * Z) * (3 * Z) + 2 * Z + 100 * Z * Z + Z := by
      gcongr <;> linarith
    _ ≤ 407 * Z ^ 2 := by nlinarith
    _ ≤ Z ^ 9 * Z ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg Z)
    _ = Z ^ 11 := by ring

/-- Transport of a quadratic preserves a fixed polynomial coefficient bound. -/
theorem coefficient_polynomial_budget {Z A H : ℝ} (hZ : 2 ≤ Z)
    (hA0 : 0 ≤ A) (hA : A ≤ Z) (hH0 : 0 ≤ H) (hH : H ≤ Z ^ 11) :
    81 * A * H ^ 2 ≤ Z ^ 30 := by
  have hc : (81 : ℝ) ≤ Z ^ 7 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hZ 7
    norm_num at this
    linarith
  calc
    81 * A * H ^ 2 ≤ 81 * Z * (Z ^ 11) ^ 2 := by gcongr
    _ = 81 * Z ^ 23 := by ring
    _ ≤ Z ^ 7 * Z ^ 23 := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = Z ^ 30 := by ring

end Submission.Obl.k4_compatible_pair_frame_preparation
