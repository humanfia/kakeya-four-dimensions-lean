import Mathlib

/-! Elementary bookkeeping for the frozen calibration constant. The Remez
loss of the grid kernel is taken at the truncated mass `min m (β (8K)^3)`,
which always satisfies the kernel's side condition; its loss is still bounded
by a fixed power of `1 + K` times `(1 + β/m)^6`. -/

namespace Submission.Obl.k4_quadratic_mesh_coefficient_calibration

/-- The degree-two Remez loss at the truncated mass. -/
theorem truncated_remez_loss_le {K β m : ℝ} (hK : 1 ≤ K) (hβ : 0 < β) (hm : 0 < m) :
    (32 * (((2 : ℕ) : ℝ) + 1) / (min m (β * (8 * K) ^ 3) / (β * (8 * K) ^ 3))) ^ (3 * 2) ≤
      96 ^ 6 * 8 ^ 18 * (1 + K) ^ 18 * (1 + β / m) ^ 6 := by
  have hB : 0 < β * (8 * K) ^ 3 := by positivity
  have hm' : 0 < min m (β * (8 * K) ^ 3) := lt_min hm hB
  have hβm : 0 < β / m := div_pos hβ hm
  have hratio : (β * (8 * K) ^ 3) / min m (β * (8 * K) ^ 3) ≤
      (8 * K) ^ 3 * (1 + β / m) := by
    rcases le_total m (β * (8 * K) ^ 3) with h | h
    · rw [min_eq_left h, div_le_iff₀ hm]
      have hmul : β / m * m = β := div_mul_cancel₀ β hm.ne'
      have h8 : 0 ≤ (8 * K) ^ 3 := by positivity
      nlinarith
    · rw [min_eq_right h, div_self hB.ne']
      have h1 : 1 ≤ (8 * K) ^ 3 := one_le_pow₀ (by linarith)
      nlinarith
  have heq : 32 * (((2 : ℕ) : ℝ) + 1) / (min m (β * (8 * K) ^ 3) / (β * (8 * K) ^ 3)) =
      96 * ((β * (8 * K) ^ 3) / min m (β * (8 * K) ^ 3)) := by
    rw [div_div_eq_mul_div]
    push_cast
    ring
  have hbase : 32 * (((2 : ℕ) : ℝ) + 1) / (min m (β * (8 * K) ^ 3) / (β * (8 * K) ^ 3)) ≤
      96 * ((8 * K) ^ 3 * (1 + β / m)) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left hratio (by norm_num)
  calc
    _ ≤ (96 * ((8 * K) ^ 3 * (1 + β / m))) ^ (3 * 2) :=
      pow_le_pow_left₀ (by rw [heq]; positivity) hbase _
    _ = 96 ^ 6 * 8 ^ 18 * K ^ 18 * (1 + β / m) ^ 6 := by ring
    _ ≤ 96 ^ 6 * 8 ^ 18 * (1 + K) ^ 18 * (1 + β / m) ^ 6 := by
      gcongr
      linarith

end Submission.Obl.k4_quadratic_mesh_coefficient_calibration
