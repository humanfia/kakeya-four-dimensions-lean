import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Submission.Obl.k4_finite_affine_parent_sources

/-- The fixed sample budget pays both the original parent floor and the
numerical factor in the palette coefficient. -/
theorem sample_palette_floor_budget (m : ℕ) {κ K A : ℝ}
    (hκ : 1 ≤ κ) (hK : 1 ≤ K)
    (hA : (10 : ℝ) ^ 40 * κ ^ 20 * K ^ 4 * ((m : ℝ) + 2) ^ 4 ≤ A) :
    10000 * κ ^ 2 ≤ A ∧ 64 * (m : ℝ) * κ ^ 2 ≤ A := by
  have hκp : κ ^ 2 ≤ κ ^ 20 := pow_le_pow_right₀ hκ (by norm_num)
  have hKp : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hm1 : 1 ≤ ((m : ℝ) + 2) ^ 4 :=
    one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hm : (m : ℝ) ≤ ((m : ℝ) + 2) ^ 4 := by
    calc (m : ℝ) ≤ (m : ℝ) + 2 := by linarith
      _ ≤ ((m : ℝ) + 2) ^ 4 :=
        le_self_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by norm_num)
  constructor
  · apply le_trans _ hA
    calc 10000 * κ ^ 2 = 10000 * κ ^ 2 * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  · apply le_trans _ hA
    calc 64 * (m : ℝ) * κ ^ 2 = 64 * κ ^ 2 * 1 * (m : ℝ) := by ring
      _ ≤ _ := by gcongr <;> norm_num

/-- Five exponent losses, with three individually bounded tolerances,
fit the sixth power of the sample budget. -/
theorem sample_palette_power_budget {Nk κ b τa τd ma : ℝ}
    (hNk : 1 ≤ Nk) (hτa : τa ≤ b) (hτd : τd ≤ b) (hma : ma ≤ b)
    (hcoef : 10000 * κ ^ 2 ≤ Nk ^ b) :
    10000 * κ ^ 2 * Nk ^ (τa + τd + b + b + ma) ≤ (Nk ^ b) ^ 6 := by
  have hNk0 : 0 < Nk := by linarith
  have hexp : τa + τd + b + b + ma ≤ 5 * b := by linarith
  calc 10000 * κ ^ 2 * Nk ^ (τa + τd + b + b + ma)
      ≤ Nk ^ b * Nk ^ (5 * b) :=
        mul_le_mul hcoef (Real.rpow_le_rpow_of_exponent_le hNk hexp)
          (by positivity) (by positivity)
    _ = (Nk ^ b) ^ 6 := by
      rw [← Real.rpow_add hNk0, ← Real.rpow_mul_natCast hNk0.le]
      congr 1
      ring

/-- A packet floor paid by the sample budget is also the required
original-reference floor. -/
theorem sample_palette_inverse_floor {Nk b κ : ℝ} {m : ℕ}
    (hNk : 0 < Nk) (hm : 0 < m) (hκ : 0 < κ)
    (hA : 64 * (m : ℝ) * κ ^ 2 ≤ Nk ^ b) :
    Nk ^ (-b) ≤ 1 / (64 * (m : ℝ) * κ ^ 2) := by
  rw [Real.rpow_neg hNk.le, one_div]
  exact inv_anti₀ (by positivity) hA

end Submission.Obl.k4_finite_affine_parent_sources
