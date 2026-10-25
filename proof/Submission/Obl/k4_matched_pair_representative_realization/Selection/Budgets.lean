import Mathlib

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

/-- One fixed integer exponent absorbs the physical substitution coefficients
and both Boolean format budgets, independently of the final slack. -/
theorem chart_budgets {N m : ℝ} {M Me Z : ℕ} (hN : 2 ≤ N) (hMZ : M ≤ Z)
    (hm : m ≤ N ^ M) :
    let M' := max Me (M + 4 * Z) + 16
    M ≤ M' ∧
      81 * N ^ M * (6 * (N ^ Z) ^ 2) ^ 2 ≤ N ^ M' ∧
      m * N ^ M + 14 ≤ N ^ M' ∧
      N ^ Me + ((m * N ^ M + 14) + (2 + m * N ^ M)) ≤ N ^ M' := by
  dsimp only
  let e := max Me (M + 4 * Z)
  have hN0 : 0 ≤ N := (by norm_num : (0 : ℝ) ≤ 2).trans hN
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans hN
  have hMe : M ≤ e := by dsimp [e]; omega
  have h2Me : 2 * M ≤ e := by dsimp [e]; omega
  have he1 : 1 ≤ N ^ e := one_le_pow₀ hN1
  have hbig : (65536 : ℝ) ≤ N ^ 16 := by
    exact le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 16)
  have hmul : m * N ^ M ≤ N ^ e := by
    calc _ ≤ N ^ M * N ^ M := mul_le_mul_of_nonneg_right hm (pow_nonneg hN0 _)
         _ = N ^ (2 * M) := by rw [two_mul, pow_add]
         _ ≤ _ := pow_le_pow_right₀ hN1 h2Me
  have hMe' : N ^ Me ≤ N ^ e := pow_le_pow_right₀ hN1 (le_max_left _ _)
  have htarget : 65536 * N ^ e ≤ N ^ (e + 16) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right hbig (pow_nonneg hN0 _) |>.trans_eq (mul_comm _ _)
  have hcoef : 81 * N ^ M * (6 * (N ^ Z) ^ 2) ^ 2 = 2916 * N ^ (M + 4 * Z) := by
    rw [Nat.mul_comm 4 Z, pow_add, pow_mul]
    ring
  have hcoef' : 81 * N ^ M * (6 * (N ^ Z) ^ 2) ^ 2 ≤ N ^ (e + 16) := by
    rw [hcoef]
    calc _ ≤ 2916 * N ^ e := mul_le_mul_of_nonneg_left
           (pow_le_pow_right₀ hN1 (le_max_right _ _)) (by norm_num)
         _ ≤ 65536 * N ^ e := by nlinarith
         _ ≤ _ := htarget
  have hF : N ^ Me + ((m * N ^ M + 14) + (2 + m * N ^ M)) ≤ N ^ (e + 16) := by
    have hsmall : N ^ Me + ((m * N ^ M + 14) + (2 + m * N ^ M)) ≤ 65536 * N ^ e := by
      nlinarith
    exact hsmall.trans htarget
  have hA : m * N ^ M + 14 ≤ N ^ (e + 16) := by
    calc _ ≤ N ^ e + 14 := by linarith
         _ ≤ 65536 * N ^ e := by nlinarith
         _ ≤ _ := htarget
  exact ⟨by omega, hcoef', hA, hF⟩

end Submission.Obl.k4_matched_pair_representative_realization.Selection
