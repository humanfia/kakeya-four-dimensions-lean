-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0812 f7bed5fb, x0891 a669339c, x0923 e8a77b3e, x0807 989bea46 (SourceParentPalette: x0812's version); namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceKeptEH2

/-! Explicit power budgets for the kept source cell bounds. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- The reference pure cap uses four small budget powers: one for its fixed slack cost,
one for rounding to the density grid, and two for the density and path errors. -/
theorem pureConst_le_rpow {Nk κ hd τd δ₀ L b : ℝ}
    (hN : 1 ≤ Nk) (hκ : 1 ≤ κ) (hb : 0 ≤ b) (hhd : hd ≤ b)
    (hτ : τd + 2 * (δ₀ * L) ≤ 2 * b) (hpoly : 192 * κ ^ 3 ≤ Nk ^ b) :
    pureConst κ Nk hd τd δ₀ L ≤ Nk ^ (4 * b) := by
  have hN0 : 0 < Nk := zero_lt_one.trans_le hN
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  have hNb : 1 ≤ Nk ^ b := Real.one_le_rpow hN hb
  have hcell : 4 * Nk ^ hd + 2 ≤ 6 * Nk ^ b := by
    have h := Real.rpow_le_rpow_of_exponent_le hN hhd
    linarith
  have hslack : 16 * (1 + κ ^ 2) ≤ 32 * κ ^ 2 := by
    nlinarith [sq_nonneg (κ - 1)]
  have hExp := Real.rpow_le_rpow_of_exponent_le hN hτ
  calc
    pureConst κ Nk hd τd δ₀ L ≤ κ * (6 * Nk ^ b) * Nk ^ (2 * b) * (32 * κ ^ 2) := by
      unfold pureConst
      have h₁ := mul_le_mul_of_nonneg_left hcell hκ0
      have h₂ := mul_le_mul h₁ hExp (by positivity) (by positivity)
      exact mul_le_mul h₂ hslack (by positivity) (by positivity)
    _ = (192 * κ ^ 3) * (Nk ^ b * Nk ^ (2 * b)) := by ring
    _ ≤ Nk ^ b * (Nk ^ b * Nk ^ (2 * b)) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = Nk ^ (4 * b) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1
      ring

/-- A single factor `20` in a small power pays the quadratic raw-cap upgrade cost. -/
theorem quadratic_cap_power_cost {Nk b a A : ℝ} (hN : 1 ≤ Nk) (hb : 0 ≤ b)
    (h20 : 20 ≤ Nk ^ b) (hA : 2 * a + 2 ≤ A) :
    400 * (Nk ^ (a * b)) ^ 2 ≤ Nk ^ (A * b) := by
  have hN0 : 0 < Nk := zero_lt_one.trans_le hN
  have h400 : 400 ≤ Nk ^ (2 * b) := by
    calc (400 : ℝ) = (20 : ℝ) ^ 2 := by norm_num
      _ ≤ (Nk ^ b) ^ 2 := pow_le_pow_left₀ (by norm_num) h20 2
      _ = _ := by rw [← Real.rpow_mul_natCast hN0.le]; congr 1; ring
  calc
    400 * (Nk ^ (a * b)) ^ 2 ≤ Nk ^ (2 * b) * (Nk ^ (a * b)) ^ 2 :=
      mul_le_mul_of_nonneg_right h400 (sq_nonneg _)
    _ = Nk ^ ((2 * a + 2) * b) := by
      rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_add hN0]
      congr 1
      ring
    _ ≤ Nk ^ (A * b) := Real.rpow_le_rpow_of_exponent_le hN
      (mul_le_mul_of_nonneg_right hA hb)

end

end Submission.Obl.k4_finite_affine_parent_sources
