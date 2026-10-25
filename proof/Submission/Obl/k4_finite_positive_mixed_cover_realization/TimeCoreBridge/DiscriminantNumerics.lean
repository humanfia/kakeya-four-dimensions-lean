-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/DiscriminantNumerics.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Mathlib

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

/-- Uniform original discriminant allowance, written using the original projection
fraction and the full normalized old-packet radius. -/
noncomputable def discriminantAllowance (Cdisc N κ loss fitExponent : ℝ) : ℝ :=
  Cdisc * (96 / ((N ^ (-loss) / (64 * κ)) / (8 * (κ + 1)) ^ 3)) ^ 6 *
    (3 * ((N ^ fitExponent) ^ 2 + κ ^ 2))

noncomputable def discriminantConstant (Cdisc : ℝ) : ℝ :=
  Cdisc * (96 * 64 * 512 : ℝ) ^ 6 * (3 * 2 ^ (19 : ℕ))

/-- All original-discriminant losses are powers of the input slacks, with a fixed
multiplicative constant. The radius and fraction contribute only κ^24. -/
theorem discriminant_allowance_power_bound {N κ σ Cdisc loss fitExponent : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N ^ σ) (hσ : 0 ≤ σ)
    (hC : 0 ≤ Cdisc) (hfit : 0 ≤ fitExponent) :
    discriminantAllowance Cdisc N κ loss fitExponent ≤
      discriminantConstant Cdisc * N ^ (6 * loss + 2 * fitExponent + 26 * σ) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  have hκplus : 0 < κ + 1 := by positivity
  have hpow (a : ℝ) (k : ℕ) : (N ^ a) ^ k = N ^ ((k : ℝ) * a) := by
    rw [← Real.rpow_mul_natCast hNpos.le]
    congr 1
    ring
  have hratio : 96 / ((N ^ (-loss) / (64 * κ)) / (8 * (κ + 1)) ^ 3) =
      (96 * 64 * 512 : ℝ) * κ * (κ + 1) ^ 3 * N ^ loss := by
    rw [Real.rpow_neg hNpos.le]
    field_simp [(Real.rpow_pos_of_pos hNpos loss).ne', hκpos.ne', hκplus.ne']
    ring
  have hexpand : ((96 * 64 * 512 : ℝ) * κ * (κ + 1) ^ 3 * N ^ loss) ^ 6 =
      (96 * 64 * 512 : ℝ) ^ 6 * (κ ^ 6 * (κ + 1) ^ 18) * N ^ (6 * loss) := by
    rw [mul_pow, mul_pow, mul_pow, hpow, ← pow_mul (κ + 1) 3 6]
    norm_num only [Nat.reduceMul, Nat.cast_ofNat]
    ring
  have hκpart : κ ^ 6 * (κ + 1) ^ 18 ≤ (2 : ℝ) ^ (18 : ℕ) * N ^ (24 * σ) := by
    calc
      _ ≤ κ ^ 6 * (2 * κ) ^ 18 := by gcongr; linarith
      _ = 2 ^ (18 : ℕ) * κ ^ 24 := by ring
      _ ≤ 2 ^ (18 : ℕ) * (N ^ σ) ^ 24 := by gcongr
      _ = _ := by rw [hpow]; norm_num
  have hU : 1 ≤ (N ^ fitExponent) ^ 2 := one_le_pow₀ (Real.one_le_rpow hN hfit)
  have hV : 1 ≤ (N ^ σ) ^ 2 := one_le_pow₀ (Real.one_le_rpow hN hσ)
  have hsum : (N ^ fitExponent) ^ 2 + κ ^ 2 ≤ 2 * N ^ (2 * fitExponent + 2 * σ) := by
    calc
      _ ≤ (N ^ fitExponent) ^ 2 + (N ^ σ) ^ 2 := by gcongr
      _ ≤ 2 * ((N ^ fitExponent) ^ 2 * (N ^ σ) ^ 2) := by
        have ha := le_mul_of_one_le_right (sq_nonneg (N ^ fitExponent)) hV
        have hb := le_mul_of_one_le_left (sq_nonneg (N ^ σ)) hU
        linarith
      _ = _ := by rw [hpow, hpow, ← Real.rpow_add hNpos]; norm_num
  calc
    _ = Cdisc * (96 * 64 * 512 : ℝ) ^ 6 * (κ ^ 6 * (κ + 1) ^ 18) * N ^ (6 * loss) *
        (3 * ((N ^ fitExponent) ^ 2 + κ ^ 2)) := by
      rw [discriminantAllowance, hratio, hexpand]
      ring
    _ ≤ Cdisc * (96 * 64 * 512 : ℝ) ^ 6 * (2 ^ (18 : ℕ) * N ^ (24 * σ)) * N ^ (6 * loss) *
        (3 * (2 * N ^ (2 * fitExponent + 2 * σ))) := by
      gcongr
    _ = discriminantConstant Cdisc * N ^ (6 * loss + 2 * fitExponent + 26 * σ) := by
      rw [discriminantConstant]
      rw [show 6 * loss + 2 * fitExponent + 26 * σ = (24 * σ + 6 * loss) + (2 * fitExponent + 2 * σ) by ring]
      simp_rw [Real.rpow_add hNpos]
      ring

/-- The near-linearity tolerance contributes no independent loss exponent. -/
theorem sample_discriminant_exponent_bound {N κ σ Cdisc ρ gain L δ₀ ε τ : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N ^ σ) (hσ : 0 ≤ σ) (hC : 0 ≤ Cdisc)
    (hρ : 0 ≤ ρ) (hgain : 0 ≤ gain) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hδρ : δ₀ ≤ ρ * gain) :
    discriminantAllowance Cdisc N κ ((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ)
      (4 * ρ * gain * L + 4 * ε) ≤
      discriminantConstant Cdisc * N ^ (110 * ρ * gain * L + 80 * ε + 6 * τ + 26 * σ) := by
  have h1 := discriminant_allowance_power_bound (loss := (12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ)
    hN hκ hκN hσ hC (by positivity : 0 ≤ 4 * ρ * gain * L + 4 * ε)
  apply h1.trans
  apply mul_le_mul_of_nonneg_left _ (by dsimp only [discriminantConstant]; positivity)
  apply Real.rpow_le_rpow_of_exponent_le hN
  nlinarith [mul_le_mul_of_nonneg_right hδρ hL]

/-- A single fixed positive ρ·gain·L power absorbs the constant in the universal
coefficient bound, uniformly over all smaller ε and σ. -/
theorem sample_discriminant_power_allowance {N κ σ Cdisc ρ gain L δ₀ ε τ : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N ^ σ) (hσ : 0 ≤ σ) (hC : 0 ≤ Cdisc)
    (hρ : 0 ≤ ρ) (hgain : 0 ≤ gain) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hδρ : δ₀ ≤ ρ * gain)
    (hconstant : discriminantConstant Cdisc ≤ N ^ (90 * ρ * gain * L)) :
    discriminantAllowance Cdisc N κ ((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ)
      (4 * ρ * gain * L + 4 * ε) ≤ N ^ (200 * (ρ * gain * L + ε + σ + τ)) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have h1 := sample_discriminant_exponent_bound (τ := τ) hN hκ hκN hσ hC hρ hgain hL hε hδρ
  calc
    _ ≤ discriminantConstant Cdisc * N ^ (110 * ρ * gain * L + 80 * ε + 6 * τ + 26 * σ) := h1
    _ ≤ N ^ (90 * ρ * gain * L) * N ^ (110 * ρ * gain * L + 80 * ε + 6 * τ + 26 * σ) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = N ^ (200 * ρ * gain * L + 80 * ε + 6 * τ + 26 * σ) := by rw [← Real.rpow_add hNpos]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
