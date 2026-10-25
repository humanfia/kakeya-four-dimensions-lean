import Submission.Obl.k4_scalar_grid_cartesian_field.Growth

namespace Submission.Obl.k4_scalar_grid_cartesian_field

noncomputable def finalBudget (C Λ : ℝ) (q : ℕ) : ℝ := (8 * max 1 C) * Λ ^ (q + 4)

/-- One polynomial envelope dominates the original, interpolation and final-pruning losses. -/
theorem finalBudget_bounds {C Λ : ℝ} (hC : 0 < C) (hΛ : 1 ≤ Λ) (q : ℕ) :
    1 ≤ finalBudget C Λ q ∧ 2 * Λ ≤ finalBudget C Λ q ∧
      C * Λ ^ q ≤ finalBudget C Λ q ∧
      4 * C * Λ ^ (q + 3) ≤ finalBudget C Λ q ∧
      2 * C * Λ ^ (q + 1) ≤ finalBudget C Λ q := by
  have hmax : 1 ≤ max 1 C := le_max_left _ _
  have hCmax : C ≤ max 1 C := le_max_right _ _
  have hpow : 1 ≤ Λ ^ (q + 4) := one_le_pow₀ hΛ
  have hpow₁ : Λ ≤ Λ ^ (q + 4) := by
    simpa only [pow_one] using pow_le_pow_right₀ hΛ (show 1 ≤ q + 4 by omega)
  have hpowq : Λ ^ q ≤ Λ ^ (q + 4) := pow_le_pow_right₀ hΛ (by omega)
  have hpowq₃ : Λ ^ (q + 3) ≤ Λ ^ (q + 4) := pow_le_pow_right₀ hΛ (by omega)
  have hpowq₁ : Λ ^ (q + 1) ≤ Λ ^ (q + 4) := pow_le_pow_right₀ hΛ (by omega)
  have hcommon : 0 ≤ max 1 C * Λ ^ (q + 4) := by positivity
  unfold finalBudget
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul hmax hpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ max 1 C)]
  · calc
      _ ≤ 2 * Λ ^ (q + 4) := mul_le_mul_of_nonneg_left hpow₁ (by norm_num)
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ max 1 C * Λ ^ (q + 4) := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ 4 * max 1 C * Λ ^ (q + 4) := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ 2 * max 1 C * Λ ^ (q + 4) := by gcongr
      _ ≤ _ := by nlinarith

/-- The common final envelope preserves the frozen subpower convention. -/
theorem finalBudget_subpower {data : Data} (hscale : scaleHyp data)
    {Λ : ℕ → ℝ} (hΛ : subpower data Λ) {C : ℝ} (hC : 0 < C) (q : ℕ) :
    subpower data (fun k => finalBudget C (Λ k) q) := by
  exact Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
    (fun k => by linarith [hscale.1 k]) hscale.2.1 hΛ
    (show 1 ≤ 8 * max 1 C by linarith [le_max_left (1 : ℝ) C]) (q + 4)

end Submission.Obl.k4_scalar_grid_cartesian_field
