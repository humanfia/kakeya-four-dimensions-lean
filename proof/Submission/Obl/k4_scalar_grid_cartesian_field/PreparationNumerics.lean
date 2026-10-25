import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field

/-- Invert a positive lower mass floor without altering the original reference mass. -/
theorem original_budget_of_mass_floor {a : ℝ} (ha : 0 < a) {P mass : ENNReal}
    (hfloor : ENNReal.ofReal a * P ≤ mass) : P ≤ ENNReal.ofReal a⁻¹ * mass := by
  have hne : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  calc
    _ = ENNReal.ofReal a⁻¹ * (ENNReal.ofReal a * P) := by
      rw [ENNReal.ofReal_inv_of_pos ha, ← mul_assoc,
        ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hfloor

/-- An original full-prior ceiling becomes relative to a retained packet mass. -/
theorem cap_from_original_prior {C D Λ h ξ : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hh : 0 ≤ h)
    (hCD : C * D ≤ Λ) {m mass cell : ENNReal}
    (hcap : cell ≤ ENNReal.ofReal (C * h * ξ ^ 2) * m)
    (hbudget : ENNReal.ofReal h * m ≤ ENNReal.ofReal D * mass) :
    cell ≤ ENNReal.ofReal (Λ * ξ ^ 2) * mass := by
  calc
    _ ≤ ENNReal.ofReal (C * h * ξ ^ 2) * m := hcap
    _ = ENNReal.ofReal (C * ξ ^ 2) * (ENNReal.ofReal h * m) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * ξ ^ 2)]
      congr 2
      ring
    _ ≤ ENNReal.ofReal (C * ξ ^ 2) * (ENNReal.ofReal D * mass) := mul_le_mul' le_rfl hbudget
    _ = ENNReal.ofReal ((C * D) * ξ ^ 2) * mass := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * ξ ^ 2)]
      congr 2
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCD (sq_nonneg ξ))) le_rfl

noncomputable def preparationBudget (W : ℝ) : ℝ := 1000000000 * W ^ 20

/-- A fixed common envelope absorbs all outer polynomial losses. -/
theorem preparationBudget_polynomial {W A : ℝ} (hW : 1 ≤ W) (hA : 0 ≤ A)
    (hAmax : A ≤ 1000000000) {p : ℕ} (hp : p ≤ 20) :
    A * W ^ p ≤ preparationBudget W := by
  exact mul_le_mul hAmax (pow_le_pow_right₀ hW hp) (by positivity) (by norm_num)

theorem preparationBudget_base {W : ℝ} (hW : 1 ≤ W) : 1 ≤ preparationBudget W ∧ W ≤ preparationBudget W := by
  have hpow : 1 ≤ W ^ 20 := one_le_pow₀ hW
  have hWpow : W ≤ W ^ 20 := by simpa only [pow_one] using pow_le_pow_right₀ hW (show 1 ≤ 20 by norm_num)
  unfold preparationBudget
  constructor <;> nlinarith

structure PreparationBudgetBounds (K L H₀ H Λ : ℝ) : Prop where
  original : K ≤ Λ
  reference : H₀ ≤ Λ
  graph : H ≤ Λ
  layer : L ≤ Λ
  fine : 8000 * L ^ 3 * H₀ ^ 4 * K ≤ Λ
  palette : 256000 * K ^ 2 * L ^ 3 * H₀ ^ 4 * H ≤ Λ
  relative_base : 1600000 * K ^ 7 * H ≤ Λ
  joint : 32000 * L ^ 3 * H₀ ^ 2 ≤ Λ

/-- The explicit common envelope covers every loss in the pointwise packet constructor. -/
theorem preparationBudget_bounds {K L H₀ H W : ℝ}
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hH₀ : 1 ≤ H₀) (hH : 1 ≤ H)
    (hKW : K ≤ W) (hLW : L ≤ W) (hH₀W : H₀ ≤ W) (hHW : H ≤ W) :
    PreparationBudgetBounds K L H₀ H (preparationBudget W) := by
  have hW : 1 ≤ W := hK.trans hKW
  have hWp := (preparationBudget_base hW).2
  refine ⟨hKW.trans hWp, hH₀W.trans hWp, hHW.trans hWp, hLW.trans hWp, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ 8000 * W ^ 3 * W ^ 4 * W := by gcongr
      _ = 8000 * W ^ 8 := by ring
      _ ≤ _ := preparationBudget_polynomial hW (by norm_num) (by norm_num) (show 8 ≤ 20 by norm_num)
  · calc
      _ ≤ 256000 * W ^ 2 * W ^ 3 * W ^ 4 * W := by gcongr
      _ = 256000 * W ^ 10 := by ring
      _ ≤ _ := preparationBudget_polynomial hW (by norm_num) (by norm_num) (show 10 ≤ 20 by norm_num)
  · calc
      _ ≤ 1600000 * W ^ 7 * W := by gcongr
      _ = 1600000 * W ^ 8 := by ring
      _ ≤ _ := preparationBudget_polynomial hW (by norm_num) (by norm_num) (show 8 ≤ 20 by norm_num)
  · calc
      _ ≤ 32000 * W ^ 3 * W ^ 2 := by gcongr
      _ = 32000 * W ^ 5 := by ring
      _ ≤ _ := preparationBudget_polynomial hW (by norm_num) (by norm_num) (show 5 ≤ 20 by norm_num)

end Submission.Obl.k4_scalar_grid_cartesian_field
