import Submission.Obl.k4_row_cell_regularization.Budget

namespace Submission.Obl.k4_row_cell_regularization

/-- The final loss absorbs every polynomial factor produced by the original cells and
one comparable palette level. -/
theorem lossK_bounds {J : ℕ} {L : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) :
    (L + 1 ≤ lossK J L) ∧
    (8 * L ^ 2 ≤ lossK J L) ∧
    (2 ^ 18 * L ^ 6 ≤ lossK J L) ∧
    (4 * L * (J : ℝ) ≤ lossK J L) ∧
    (L ^ 2 ≤ lossK J L) ∧
    (32 * (J : ℝ) * L ^ 6 ≤ lossK J L) := by
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hp (n : ℕ) (hn : n ≤ 8) : L ^ n ≤ L ^ 8 := pow_le_pow_right₀ hL hn
  have hC : (2 : ℝ) ^ 30 ≤ 2 ^ 30 * (J : ℝ) := by nlinarith
  have habs (A : ℝ) (n : ℕ) (hA : 0 ≤ A) (hAC : A ≤ 2 ^ 30 * (J : ℝ))
      (hn : n ≤ 8) : A * L ^ n ≤ lossK J L := by
    exact mul_le_mul hAC (hp n hn) (pow_nonneg hL0 _) (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc L + 1 ≤ 2 * L := by linarith
      _ = 2 * L ^ 1 := by ring
      _ ≤ lossK J L := habs 2 1 (by norm_num) (by norm_num at hC ⊢; linarith) (by norm_num)
  · exact habs 8 2 (by norm_num) (by norm_num at hC ⊢; linarith) (by norm_num)
  · exact habs (2 ^ 18) 6 (by positivity) (by norm_num at hC ⊢; linarith) (by norm_num)
  · have he := habs (4 * (J : ℝ)) 1 (by positivity)
      (mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 2 ^ 30) hJ0) (by norm_num)
    simpa only [pow_one, mul_comm, mul_left_comm] using he
  · have he := habs 1 2 (by norm_num) (by norm_num at hC ⊢; linarith) (by norm_num)
    simpa only [one_mul] using he
  · exact habs (32 * (J : ℝ)) 6 (by positivity)
      (mul_le_mul_of_nonneg_right (by norm_num : (32 : ℝ) ≤ 2 ^ 30) hJ0) (by norm_num)

end Submission.Obl.k4_row_cell_regularization
