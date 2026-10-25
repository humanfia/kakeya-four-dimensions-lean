import Mathlib

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedLongDomain.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

noncomputable section

def longWidth (β₀ β₁ : ℝ) : ℝ := min β₀ β₁

def longSlope (β₀ β₁ : ℝ) : ℝ := max β₀ β₁

def longTime (β₀ β₁ : ℝ) : ℝ := longWidth β₀ β₁ / longSlope β₀ β₁

structure LongDomainBounds (N C β₀ β₁ : ℝ) : Prop where
  time_pos : 0 < longTime β₀ β₁
  slope_pos : 0 < longSlope β₀ β₁
  width_pos : 0 < longWidth β₀ β₁
  time_le_one : longTime β₀ β₁ ≤ 1
  motion : longTime β₀ β₁ * longSlope β₀ β₁ ≤ longWidth β₀ β₁
  width_coarse : longWidth β₀ β₁ ≤ β₀
  width_fine : longWidth β₀ β₁ ≤ β₁
  coarse_slope : β₀ ≤ longSlope β₀ β₁
  fine_slope : β₁ ≤ longSlope β₀ β₁
  time_lower : N ^ (-C) ≤ longTime β₀ β₁
  time_upper : longTime β₀ β₁ ≤ N ^ C
  width_lower : N ^ (-C) ≤ longWidth β₀ β₁
  width_upper : longWidth β₀ β₁ ≤ N ^ C
  slope_upper : longSlope β₀ β₁ ≤ N ^ C

/-- The literal minimum and maximum moving-interval widths supply common
long domains with one fixed coarse power bound. -/
theorem long_domain_power_bounds {N H L C β₀ β₁ : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N) (hL : 0 ≤ L) (hC : L + 2 ≤ C)
    (hβ₀ : 0 < β₀) (hβ₁ : 0 < β₁)
    (hlo₀ : N ^ (-L) / H ≤ β₀) (hlo₁ : N ^ (-L) / H ≤ β₁)
    (hhi₀ : β₀ ≤ H) (hhi₁ : β₁ ≤ H) : LongDomainBounds N C β₀ β₁ := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hb : 0 < longWidth β₀ β₁ := lt_min hβ₀ hβ₁
  have hg : 0 < longSlope β₀ β₁ := hβ₀.trans_le (le_max_left _ _)
  have hbH : longWidth β₀ β₁ ≤ H := (min_le_left _ _).trans hhi₀
  have hgH : longSlope β₀ β₁ ≤ H := max_le hhi₀ hhi₁
  have hbmin : N ^ (-L) / H ≤ longWidth β₀ β₁ := le_min hlo₀ hlo₁
  have ht1 : longTime β₀ β₁ ≤ 1 := by
    apply (div_le_iff₀ hg).mpr
    simpa only [longWidth, longSlope, one_mul] using (min_le_max : min β₀ β₁ ≤ max β₀ β₁)
  have hNpow : N ≤ N ^ C := by
    calc
      _ = N ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hN2 : N ≤ N ^ 2 := le_self_pow₀ hN (by norm_num : 2 ≠ 0)
  have hH2 : H ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hHp.le hHN _
  have hpowers : N ^ (-C) * N ^ 2 ≤ N ^ (-L) := by
    calc
      _ = N ^ (2 - C) := by rw [← Real.rpow_two N, ← Real.rpow_add hNp]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hbpower : N ^ (-C) ≤ longWidth β₀ β₁ := by
    apply le_trans _ hbmin
    apply (le_div_iff₀ hHp).mpr
    exact (mul_le_mul_of_nonneg_left (hHN.trans hN2) (Real.rpow_nonneg hNp.le _)).trans hpowers
  have htpower : N ^ (-C) ≤ longTime β₀ β₁ := by
    apply (le_div_iff₀ hg).mpr
    apply le_trans _ hbmin
    apply (le_div_iff₀ hHp).mpr
    have hgH2 : longSlope β₀ β₁ * H ≤ N ^ 2 := by
      calc
        _ ≤ H * H := mul_le_mul_of_nonneg_right hgH hHp.le
        _ ≤ _ := by nlinarith
    calc
      _ = N ^ (-C) * (longSlope β₀ β₁ * H) := by ring
      _ ≤ N ^ (-C) * N ^ 2 := mul_le_mul_of_nonneg_left hgH2 (Real.rpow_nonneg hNp.le _)
      _ ≤ _ := hpowers
  exact {
    time_pos := div_pos hb hg
    slope_pos := hg
    width_pos := hb
    time_le_one := ht1
    motion := (div_mul_cancel₀ _ hg.ne').le
    width_coarse := min_le_left _ _
    width_fine := min_le_right _ _
    coarse_slope := le_max_left _ _
    fine_slope := le_max_right _ _
    time_lower := htpower
    time_upper := ht1.trans (Real.one_le_rpow hN (by linarith))
    width_lower := hbpower
    width_upper := hbH.trans (hHN.trans hNpow)
    slope_upper := hgH.trans (hHN.trans hNpow) }

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
