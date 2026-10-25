-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/SatNumerics.lean
import Submission.Obl.k4_terminal_label_saturation.SatPrune

/-!
# Numerical choices for label saturation

With `H = κ' = 3200 κ₀⁶ N^τ`, `θ = N^-c`, `cap = N^(-F+τ)`, `n₀ = N^-F` the loss
budget of `saturate_prune_sample` holds as soon as `8 κ₀ ≤ N^c`; the format
budgets are polynomial in `N`.
-/

namespace Submission.Obl.k4_terminal_label_saturation

open MeasureTheory Set
open scoped ENNReal

/-- The loss budget of `saturate_prune_sample`. -/
theorem sat_budget {Nk κ₀ τ c F : ℝ} (hNk : 1 ≤ Nk) (hκ₀ : 1 ≤ κ₀) (hτ : 0 ≤ τ)
    (hc : 8 * κ₀ ≤ Nk ^ c) :
    ENNReal.ofReal (3200 * κ₀ ^ 6 * Nk ^ τ)⁻¹ +
      (2 * ENNReal.ofReal (Nk ^ (-c)) +
        2 * ENNReal.ofReal (Nk ^ (-F + τ) * (Real.pi * κ₀ ^ 3 * (14 + 48 * κ₀ ^ 2)) /
          (Nk ^ (-F) * (3200 * κ₀ ^ 6 * Nk ^ τ))) * 2 +
        ENNReal.ofReal (κ₀ / (3200 * κ₀ ^ 6 * Nk ^ τ)) * 2) ≤ ENNReal.ofReal κ₀⁻¹ := by
  have hNk0 : 0 < Nk := lt_of_lt_of_le one_pos hNk
  have hκ0 : 0 < κ₀ := lt_of_lt_of_le one_pos hκ₀
  have hτ1 : 1 ≤ Nk ^ τ := Real.one_le_rpow hNk hτ
  have hτ0 : 0 < Nk ^ τ := Real.rpow_pos_of_pos hNk0 τ
  have hF0 : 0 < Nk ^ (-F) := Real.rpow_pos_of_pos hNk0 _
  have hFτ : Nk ^ (-F + τ) = Nk ^ (-F) * Nk ^ τ := Real.rpow_add hNk0 _ _
  have hcpos : 0 < Nk ^ c := lt_of_lt_of_le (by positivity) hc
  have hθ : Nk ^ (-c) = (Nk ^ c)⁻¹ := Real.rpow_neg hNk0.le c
  -- the four real terms
  set H := 3200 * κ₀ ^ 6 * Nk ^ τ with hH
  have hH0 : 0 < H := by positivity
  have hκ6 : κ₀ ≤ κ₀ ^ 6 := by
    calc κ₀ = κ₀ ^ 1 := (pow_one κ₀).symm
      _ ≤ κ₀ ^ 6 := pow_le_pow_right₀ hκ₀ (by norm_num)
  have hHge : 3200 * κ₀ ≤ H := by
    calc 3200 * κ₀ ≤ 3200 * κ₀ ^ 6 := by linarith
      _ = 3200 * κ₀ ^ 6 * 1 := by ring
      _ ≤ H := by rw [hH]; exact mul_le_mul_of_nonneg_left hτ1 (by positivity)
  have t1 : H⁻¹ ≤ (3200 * κ₀)⁻¹ := inv_anti₀ (by positivity) hHge
  have t2 : Nk ^ (-c) ≤ (8 * κ₀)⁻¹ := by
    rw [hθ]; exact inv_anti₀ (by positivity) hc
  have t3 : Nk ^ (-F + τ) * (Real.pi * κ₀ ^ 3 * (14 + 48 * κ₀ ^ 2)) / (Nk ^ (-F) * H) ≤
      62 * Real.pi / (3200 * κ₀) := by
    rw [hFτ, hH, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk2 : 14 + 48 * κ₀ ^ 2 ≤ 62 * κ₀ ^ 2 := by nlinarith
    have hpi := Real.pi_pos
    have : Nk ^ (-F) * Nk ^ τ * (Real.pi * κ₀ ^ 3 * (14 + 48 * κ₀ ^ 2)) * (3200 * κ₀) ≤
        Nk ^ (-F) * Nk ^ τ * (Real.pi * κ₀ ^ 3 * (62 * κ₀ ^ 2)) * (3200 * κ₀) := by
      gcongr
    calc Nk ^ (-F) * Nk ^ τ * (Real.pi * κ₀ ^ 3 * (14 + 48 * κ₀ ^ 2)) * (3200 * κ₀)
        ≤ Nk ^ (-F) * Nk ^ τ * (Real.pi * κ₀ ^ 3 * (62 * κ₀ ^ 2)) * (3200 * κ₀) := this
      _ = 62 * Real.pi * (Nk ^ (-F) * (3200 * κ₀ ^ 6 * Nk ^ τ)) := by ring
  have t4 : κ₀ / H ≤ (3200 * κ₀)⁻¹ := by
    rw [div_le_iff₀ hH0]
    calc κ₀ = (3200 * κ₀)⁻¹ * (3200 * κ₀ ^ 2) := by field_simp
      _ ≤ (3200 * κ₀)⁻¹ * H := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hk : κ₀ ^ 2 ≤ κ₀ ^ 6 := pow_le_pow_right₀ hκ₀ (by norm_num)
          calc 3200 * κ₀ ^ 2 ≤ 3200 * κ₀ ^ 6 := by linarith
            _ = 3200 * κ₀ ^ 6 * 1 := by ring
            _ ≤ H := by rw [hH]; exact mul_le_mul_of_nonneg_left hτ1 (by positivity)
  -- assemble in ENNReal
  have hreal : H⁻¹ + (2 * Nk ^ (-c) + 2 * (Nk ^ (-F + τ) * (Real.pi * κ₀ ^ 3 * (14 + 48 * κ₀ ^ 2)) /
      (Nk ^ (-F) * H)) * 2 + κ₀ / H * 2) ≤ κ₀⁻¹ := by
    have hpi : Real.pi ≤ 3.15 := Real.pi_lt_d2.le.trans (by norm_num)
    have hκinv : (3200 * κ₀)⁻¹ = κ₀⁻¹ / 3200 := by field_simp
    have h8 : (8 * κ₀)⁻¹ = κ₀⁻¹ / 8 := by field_simp
    have h62 : 62 * Real.pi / (3200 * κ₀) = 62 * Real.pi / 3200 * κ₀⁻¹ := by field_simp
    have hki : 0 < κ₀⁻¹ := inv_pos.mpr hκ0
    rw [hκinv] at t1 t4
    rw [h8] at t2
    rw [h62] at t3
    nlinarith
  have hnn1 : 0 ≤ Nk ^ (-c) := (Real.rpow_pos_of_pos hNk0 _).le
  have hnn2 : 0 ≤ Nk ^ (-F + τ) * (Real.pi * κ₀ ^ 3 * (14 + 48 * κ₀ ^ 2)) / (Nk ^ (-F) * H) := by
    positivity
  have hnn3 : 0 ≤ κ₀ / H := by positivity
  calc ENNReal.ofReal H⁻¹ + (2 * ENNReal.ofReal (Nk ^ (-c)) +
        2 * ENNReal.ofReal (Nk ^ (-F + τ) * (Real.pi * κ₀ ^ 3 * (14 + 48 * κ₀ ^ 2)) /
          (Nk ^ (-F) * H)) * 2 + ENNReal.ofReal (κ₀ / H) * 2)
      = ENNReal.ofReal (H⁻¹ + (2 * Nk ^ (-c) + 2 * (Nk ^ (-F + τ) * (Real.pi * κ₀ ^ 3 *
          (14 + 48 * κ₀ ^ 2)) / (Nk ^ (-F) * H)) * 2 + κ₀ / H * 2)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hnn3]
        simp only [ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal κ₀⁻¹ := ENNReal.ofReal_le_ofReal hreal

/-- The dyadic thickness at depth `L` is at least `N^-L`. -/
theorem delta_ge_rpow {Nk L : ℝ} (hNk : 1 < Nk) (hL : 0 ≤ L) : Nk ^ (-L) ≤ δ Nk L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log Nk := Real.log_pos hNk
  unfold δ
  have hfl : (⌊L * Real.log Nk / Real.log 2⌋ : ℝ) ≤ L * Real.log Nk / Real.log 2 := Int.floor_le _
  have h2 : (2 : ℝ) ^ (-(⌊L * Real.log Nk / Real.log 2⌋ : ℤ)) =
      Real.exp (-(⌊L * Real.log Nk / Real.log 2⌋ : ℝ) * Real.log 2) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    push_cast
    ring
  have hN : Nk ^ (-L) = Real.exp (-L * Real.log Nk) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    ring_nf
  rw [h2, hN, Real.exp_le_exp]
  have : (⌊L * Real.log Nk / Real.log 2⌋ : ℝ) * Real.log 2 ≤ L * Real.log Nk := by
    calc (⌊L * Real.log Nk / Real.log 2⌋ : ℝ) * Real.log 2 ≤
        L * Real.log Nk / Real.log 2 * Real.log 2 := mul_le_mul_of_nonneg_right hfl hlog2.le
      _ = L * Real.log Nk := by field_simp
  linarith

end Submission.Obl.k4_terminal_label_saturation
