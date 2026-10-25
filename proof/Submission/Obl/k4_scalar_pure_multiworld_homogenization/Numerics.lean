import Mathlib

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

def approximationBudget (M d : ℕ) : ℕ := 10 * (M + d + 10)

theorem radius_power_bound {N : ℝ} (hN : 2 ≤ N) (M j : ℕ) :
    (2 * N ^ (M + 3)) ^ j ≤ N ^ ((M + 4) * j) := by
  calc
    _ ≤ (N * N ^ (M + 3)) ^ j :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hN (by positivity)) j
    _ = _ := by rw [← pow_succ', ← pow_mul]

theorem bin_count_power_bound {N r : ℝ} (hN : 2 ≤ N) (hr : 0 ≤ r)
    (M d : ℕ) (hrd : r ≤ (d : ℝ)) :
    2 * N ^ (M + 3) / N ^ (-r) + 5 ≤ N ^ (M + d + 6) := by
  have hN₀ : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hR : 1 ≤ N ^ (M + 3) := one_le_pow₀ hN₁
  have hNr : 1 ≤ N ^ r := Real.one_le_rpow hN₁ hr
  have hrd' : N ^ r ≤ N ^ d := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hN₁ hrd
  have hseven : (7 : ℝ) ≤ N ^ 3 := by
    calc
      (7 : ℝ) ≤ 2 ^ 3 := by norm_num
      _ ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN _
  rw [Real.rpow_neg hN₀.le, div_inv_eq_mul]
  calc
    _ ≤ 7 * N ^ (M + 3) * N ^ r := by nlinarith
    _ ≤ 7 * N ^ (M + 3) * N ^ d := by gcongr
    _ ≤ N ^ 3 * N ^ (M + 3) * N ^ d := by gcongr
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega

theorem power_mul_inv_power_le {N : ℝ} (hN : 2 ≤ N) {E H q : ℕ} (hEH : E + q ≤ H) :
    N ^ E * (N ^ H)⁻¹ ≤ (N ^ q)⁻¹ := by
  have hN₀ : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  calc
    N ^ E * (N ^ H)⁻¹ = N ^ E / N ^ H := (div_eq_mul_inv _ _).symm
    _ ≤ N ^ E / N ^ (E + q) := div_le_div_of_nonneg_left (by positivity)
      (by positivity) (pow_le_pow_right₀ hN₁ hEH)
    _ = _ := by rw [pow_add, div_mul_eq_div_div, div_self (by positivity), one_div]

theorem table_height_power_bound {N : ℝ} (hN : 2 ≤ N) (M d : ℕ) :
    N ^ (2 * M) * (2 * N ^ (M + 3)) ^ 4 ≤ N ^ approximationBudget M d := by
  have hN₁ : 1 ≤ N := by linarith
  calc
    _ ≤ N ^ (2 * M) * N ^ ((M + 4) * 4) := by
      gcongr
      exact radius_power_bound hN M 4
    _ = N ^ (2 * M + (M + 4) * 4) := (pow_add ..).symm
    _ ≤ _ := pow_le_pow_right₀ hN₁ (by dsimp [approximationBudget]; omega)

theorem straddling_power_bound {N r : ℝ} (hN : 2 ≤ N) (hr : 0 ≤ r)
    (M d H : ℕ) (hrd : r ≤ (d : ℝ)) (hH : approximationBudget M d ≤ H) :
    N ^ (2 * M) * ((2 * N ^ (M + 3) / N ^ (-r) + 5) *
      (2 * (N ^ H)⁻¹ * (2 * N ^ (M + 3)) ^ 5)) ≤ (N ^ 10)⁻¹ := by
  have hN₀ : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  calc
    _ ≤ N ^ (2 * M) * (N ^ (M + d + 6) *
        (N * (N ^ H)⁻¹ * N ^ ((M + 4) * 5))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul
      · exact bin_count_power_bound hN hr M d hrd
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_right hN (by positivity))
          (radius_power_bound hN M 5) (by positivity) (by positivity)
      · positivity
      · positivity
    _ = (N ^ (2 * M) * N ^ (M + d + 6) * N ^ 1 * N ^ ((M + 4) * 5)) *
        (N ^ H)⁻¹ := by rw [pow_one]; ring
    _ = N ^ (8 * M + d + 27) * (N ^ H)⁻¹ := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 2
      omega
    _ ≤ _ := power_mul_inv_power_le hN (by dsimp [approximationBudget] at hH; omega)

theorem cutoff_power_bound {N r : ℝ} (hN : 2 ≤ N) (hr : 0 ≤ r)
    (M d : ℕ) (hrd : r ≤ (d : ℝ)) :
    N ^ (-(approximationBudget M d : ℝ)) *
      ((2 * N ^ (M + 3)) ^ 2 * (2 * N ^ (M + 3) / N ^ (-r) + 5)) ≤
        (N ^ 10)⁻¹ := by
  have hN₀ : 0 < N := by linarith
  rw [Real.rpow_neg hN₀.le, Real.rpow_natCast]
  calc
    _ ≤ (N ^ approximationBudget M d)⁻¹ *
        (N ^ ((M + 4) * 2) * N ^ (M + d + 6)) := by
      gcongr
      · exact radius_power_bound hN M 2
      · exact bin_count_power_bound hN hr M d hrd
    _ = N ^ (3 * M + d + 14) * (N ^ approximationBudget M d)⁻¹ := by
      rw [← pow_add, mul_comm]
      congr 2
      omega
    _ ≤ _ := power_mul_inv_power_le hN (by dsimp [approximationBudget]; omega)

theorem four_error_power_bound {N : ℝ} (hN : 2 ≤ N) :
    4 * (N ^ (10 : ℕ))⁻¹ ≤ N ^ (-1 : ℝ) := by
  have hN₀ : 0 < N := by linarith
  have hfour : (4 : ℝ) ≤ N ^ 9 := by
    calc
      (4 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ N ^ 9 := pow_le_pow_left₀ (by norm_num) hN _
  calc
    _ ≤ N ^ 9 * (N ^ (10 : ℕ))⁻¹ := mul_le_mul_of_nonneg_right hfour (by positivity)
    _ = N⁻¹ := by rw [show (10 : ℕ) = 9 + 1 by omega, pow_add, pow_one, mul_inv,
      ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    _ = _ := (Real.rpow_neg_one N).symm

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
