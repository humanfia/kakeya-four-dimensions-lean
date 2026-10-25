import Mathlib

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

/-- The explicit base-cell and colored-oscillation count has a single fixed
power cost in the small tolerance. -/
theorem support_grid_power_bound {N χ d s m : ℝ} (C : ℕ)
    (hN : 2 ≤ N) (hK : 2 ≤ N ^ χ) (hm : 0 ≤ m) :
    (((2 / N ^ (-m) + 2) * (8 * N ^ χ / N ^ (-m) + 2)) *
      N ^ (d * s + χ) * (N ^ χ) ^ C *
      (4 * (N ^ χ) ^ C * N ^ (-s + χ) / N ^ (-s) + 2)) * (N ^ (-m)) ^ 2 ≤
        N ^ (d * s) * (N ^ χ) ^ (2 * C + 12) := by
  let K : ℝ := N ^ χ
  let U : ℝ := N ^ m
  let G : ℝ := K ^ C
  have hNp : 0 < N := by linarith
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK1 : 1 ≤ K := by dsimp [K]; linarith
  have hU : 1 ≤ U := Real.one_le_rpow (by linarith) hm
  have hG : 1 ≤ G := one_le_pow₀ hK1
  have hU0 : 0 ≤ U := by linarith
  have hG0 : 0 ≤ G := by linarith
  have h40 : (40 : ℝ) ≤ K ^ 6 :=
    (by norm_num : (40 : ℝ) ≤ 2 ^ 6).trans (pow_le_pow_left₀ (by norm_num) hK 6)
  have h6 : (6 : ℝ) ≤ K ^ 3 :=
    (by norm_num : (6 : ℝ) ≤ 2 ^ 3).trans (pow_le_pow_left₀ (by norm_num) hK 3)
  have hKU : 1 ≤ K * U := by
    have hh := mul_le_mul_of_nonneg_left hU hK0
    nlinarith
  have hGK : 1 ≤ G * K := by
    have hh := mul_le_mul_of_nonneg_left hK1 hG0
    nlinarith
  have hbase : (2 * U + 2) * (8 * K * U + 2) ≤ K ^ 7 * U ^ 2 := by
    calc
      _ ≤ (4 * U) * (10 * K * U) :=
        mul_le_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
      _ = 40 * (K * U ^ 2) := by ring
      _ ≤ K ^ 6 * (K * U ^ 2) :=
        mul_le_mul_of_nonneg_right h40 (mul_nonneg hK0 (sq_nonneg _))
      _ = _ := by rw [show 7 = 6 + 1 from rfl, pow_succ K 6]; ring
  have hbin : 4 * G * K + 2 ≤ G * K ^ 4 := by
    calc
      _ ≤ 6 * (G * K) := by nlinarith
      _ ≤ K ^ 3 * (G * K) :=
        mul_le_mul_of_nonneg_right h6 (mul_nonneg hG0 hK0)
      _ = _ := by rw [show 4 = 3 + 1 from rfl, pow_succ K 3]; ring
  have hdiv (a : ℝ) : a / N ^ (-m) = a * U := by
    rw [Real.rpow_neg hNp.le, div_inv_eq_mul]
  have hratio : N ^ (-s + χ) / N ^ (-s) = K := by
    rw [Real.rpow_add hNp]
    exact mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos hNp (-s)).ne'
  have hsignal : 4 * (N ^ χ) ^ C * N ^ (-s + χ) / N ^ (-s) = 4 * G * K := by
    rw [mul_div_assoc, hratio]
  have hH : N ^ (d * s + χ) = N ^ (d * s) * K := Real.rpow_add hNp _ _
  have hcancel : U ^ 2 * (N ^ (-m)) ^ 2 = 1 := by
    rw [← mul_pow]
    have hh : U * N ^ (-m) = 1 := by
      dsimp [U]
      rw [← Real.rpow_add hNp, add_neg_cancel, Real.rpow_zero]
    rw [hh, one_pow]
  have hpow : K ^ 7 * K * G * G * K ^ 4 = K ^ (2 * C + 12) := by
    dsimp [G]
    rw [← pow_succ, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  have hH0 : 0 ≤ N ^ (d * s) * K := mul_nonneg (Real.rpow_nonneg hNp.le _) hK0
  calc
    _ = ((2 * U + 2) * (8 * K * U + 2)) * (N ^ (d * s) * K) * G *
        (4 * G * K + 2) * (N ^ (-m)) ^ 2 := by
      rw [hdiv 2, hdiv (8 * N ^ χ), hH, hsignal]
    _ ≤ (K ^ 7 * U ^ 2) * (N ^ (d * s) * K) * G * (G * K ^ 4) * (N ^ (-m)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul _ hbin (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbase hH0) hG0
    _ = N ^ (d * s) * (U ^ 2 * (N ^ (-m)) ^ 2) * (K ^ 7 * K * G * G * K ^ 4) := by ring
    _ = _ := by rw [hcancel, mul_one, hpow]

theorem support_grid_target_bound {N χ η d s m : ℝ} (C : ℕ)
    (hN : 2 ≤ N) (hK : 2 ≤ N ^ χ) (hm : 0 ≤ m)
    (hχ : χ * ((2 * C + 12 : ℕ) : ℝ) ≤ η) :
    (((2 / N ^ (-m) + 2) * (8 * N ^ χ / N ^ (-m) + 2)) *
      N ^ (d * s + χ) * (N ^ χ) ^ C *
      (4 * (N ^ χ) ^ C * N ^ (-s + χ) / N ^ (-s) + 2)) * (N ^ (-m)) ^ 2 ≤
        N ^ η * (N ^ (-s)) ^ (-d) := by
  have hNp : 0 < N := by linarith
  have hpow : (N ^ χ) ^ (2 * C + 12) ≤ N ^ η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hχ
  have hds : (N ^ (-s)) ^ (-d) = N ^ (d * s) := by
    rw [← Real.rpow_mul hNp.le]
    congr 1
    ring
  calc
    _ ≤ N ^ (d * s) * (N ^ χ) ^ (2 * C + 12) := support_grid_power_bound C hN hK hm
    _ ≤ N ^ (d * s) * N ^ η := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hNp.le _)
    _ = _ := by rw [hds]; ring

end Submission.Obl.k4_unbounded_geometric_packet_reduction
