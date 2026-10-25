import Mathlib

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open Filter

/-- A strict exponent gap absorbs any fixed multiplier at large real scales. -/
theorem eventually_const_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ N : ℝ in atTop, C * N ^ a ≤ N ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C,
    eventually_ge_atTop (1 : ℝ)] with N hC hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  calc
    _ ≤ N ^ (b - a) * N ^ a :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hN0.le a)
    _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- A dimension count below the second power gives a fixed seventh-power Boolean
format bound for the twenty-four tests in each quadratic fit. -/
theorem scalar_format_count {N n d s ε : ℝ} (hN : 2 ≤ N)
    (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s) (hs1 : s < 1)
    (hε : ε ≤ 1) (hn : n ≤ N ^ (d * s + ε)) : n * 24 ≤ N ^ (7 : ℕ) := by
  have hds : d * s ≤ 1 := by nlinarith
  have hn2 : n ≤ N ^ (2 : ℕ) := by
    convert hn.trans (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N)
      (show d * s + ε ≤ 2 by linarith)) using 1 <;> norm_num
  have h24 : (24 : ℝ) ≤ N ^ (5 : ℕ) := by
    have h32 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 5
    norm_num at h32
    linarith
  calc
    _ ≤ N ^ (2 : ℕ) * 24 := mul_le_mul_of_nonneg_right hn2 (by norm_num)
    _ ≤ N ^ (2 : ℕ) * N ^ (5 : ℕ) := mul_le_mul_of_nonneg_left h24 (sq_nonneg _)
    _ = _ := by ring

end Submission.Obl.k4_fixed_budget_quadratic_recovery
