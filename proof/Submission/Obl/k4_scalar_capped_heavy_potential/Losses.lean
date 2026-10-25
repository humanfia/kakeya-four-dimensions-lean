import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open Filter

noncomputable section

def heavyOutputLoss (C H Q : ℝ) : ℝ :=
  100000000 * (1 + C) * (max H Q) ^ 10

/-- One fixed polynomial loss absorbs the heavy mass selection,
inherited palettes, improved base ceiling, and shifted coefficients. -/
theorem heavy_output_loss_bounds {C H Q : ℝ} (hC : 0 < C)
    (hH : 1 ≤ H) (hQ : 1 ≤ Q) :
    1 ≤ heavyOutputLoss C H Q ∧
      1000 * H ≤ heavyOutputLoss C H Q ∧
      735 * H ^ 2 ≤ heavyOutputLoss C H Q ∧
      3 * H ≤ heavyOutputLoss C H Q ∧
      13478400 * C * H ^ 6 * (H + 1) ^ 2 * Q ≤ heavyOutputLoss C H Q := by
  let U := max H Q
  have hU : 1 ≤ U := hH.trans (le_max_left _ _)
  have hHU : H ≤ U := le_max_left _ _
  have hQU : Q ≤ U := le_max_right _ _
  have hU₁₀ : 1 ≤ U ^ 10 := one_le_pow₀ hU
  have hUle : U ≤ U ^ 10 := by
    simpa only [pow_one] using pow_le_pow_right₀ hU (by decide : 1 ≤ (10 : ℕ))
  have hU₂ : U ^ 2 ≤ U ^ 10 := pow_le_pow_right₀ hU (by decide : 2 ≤ (10 : ℕ))
  have hH₂ : H ^ 2 ≤ U ^ 10 := (pow_le_pow_left₀ (by linarith) hHU 2).trans hU₂
  have hcoef : (1000 : ℝ) ≤ 100000000 * (1 + C) := by linarith
  have hmass : 13478400 * C * H ^ 6 * (H + 1) ^ 2 * Q ≤
      100000000 * (1 + C) * U ^ 10 := by
    calc
      _ ≤ 13478400 * C * U ^ 6 * (2 * U) ^ 2 * U := by gcongr <;> linarith
      _ = 53913600 * C * U ^ 9 := by ring
      _ ≤ 53913600 * C * U ^ 10 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU (by decide : 9 ≤ (10 : ℕ))) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  change 1 ≤ 100000000 * (1 + C) * U ^ 10 ∧ _
  refine ⟨?_, ?_, ?_, ?_, hmass⟩
  · nlinarith
  · exact (mul_le_mul_of_nonneg_left (hHU.trans hUle) (by norm_num : (0 : ℝ) ≤ 1000)).trans
      (mul_le_mul_of_nonneg_right hcoef (by positivity))
  · exact (mul_le_mul_of_nonneg_left hH₂ (by norm_num : (0 : ℝ) ≤ 735)).trans
      (mul_le_mul_of_nonneg_right (by linarith : (735 : ℝ) ≤ 100000000 * (1 + C)) (by positivity))
  · exact (mul_le_mul_of_nonneg_left (hHU.trans hUle) (by norm_num : (0 : ℝ) ≤ 3)).trans
      (mul_le_mul_of_nonneg_right (by linarith : (3 : ℝ) ≤ 100000000 * (1 + C)) (by positivity))

theorem heavy_output_loss_subpower (N H Q : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : (∀ k, 1 ≤ H k) ∧ ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, H k ≤ N k ^ e)
    (hQ : (∀ k, 1 ≤ Q k) ∧ ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, Q k ≤ N k ^ e)
    {C : ℝ} (hC : 0 < C) :
    (∀ k, 1 ≤ heavyOutputLoss C (H k) (Q k)) ∧
      ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, heavyOutputLoss C (H k) (Q k) ≤ N k ^ e := by
  exact Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial hN hNt
    (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hH hQ)
    (by linarith : (1 : ℝ) ≤ 100000000 * (1 + C)) 10

/-- Comparing the original heavy-group mass with the final common
envelope introduces no further power of the hidden-width ratio. -/
theorem heavy_mass_envelope {C H η h prior R L : ℝ}
    (hC : 0 < C) (hH : 1 ≤ H) (hη : 0 < η) (hh : 0 ≤ h)
    (hprior : 0 ≤ prior) (hR : 0 < R)
    (hL : 13478400 * C * H ^ 6 * (H + 1) ^ 2 * η⁻¹ ≤ L) :
    h * prior / (L * R) ≤ h * prior * (η / (H + 1) ^ 2) /
      (13478400 * C * H ^ 6 * R) := by
  have hH₀ : 0 < H := by linarith
  have hH₁ : H + 1 ≠ 0 := by linarith
  calc
    _ ≤ h * prior / ((13478400 * C * H ^ 6 * (H + 1) ^ 2 * η⁻¹) * R) :=
      div_le_div_of_nonneg_left (mul_nonneg hh hprior) (by positivity)
        (mul_le_mul_of_nonneg_right hL hR.le)
    _ = _ := by field_simp [hC.ne', hH₀.ne', hH₁, hη.ne', hR.ne'] <;> ring

end
end Submission.Obl.k4_scalar_capped_heavy_potential
