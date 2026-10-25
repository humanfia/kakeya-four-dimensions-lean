-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Params.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Slab.Assemble

/-!
# The power bookkeeping of the heavy windows

A window carrying at least `√s M / 60` of the mass `M ≥ δ ^ ε₁ n δ²` satisfies the volume
hypothesis of the window lemma once `C K θ⁻⁵ δ^(-3 ε₁) s ^ (ηl - ε₁) ≤ 1`.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal

lemma pieceBound_le {σ δ s θ K H : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hδ : 0 < δ) (hδs : δ ≤ s)
    (hs16 : 16 * s ≤ Real.sqrt s) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hHs : H ≤ Real.sqrt s) :
    pieceBound σ δ s θ K H ≤ 1280 * K / θ / s ^ ((1 - σ) / 2) := by
  have hs : 0 < s := hδ.trans_le hδs
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  unfold pieceBound
  -- the Assouad factor
  have h8 : (8 / Real.sqrt s) ^ (1 - σ) ≤ 8 / s ^ ((1 - σ) / 2) := by
    rw [Real.div_rpow (by norm_num) hsp.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
    have : (8 : ℝ) ^ (1 - σ) ≤ 8 := by
      calc (8 : ℝ) ^ (1 - σ) ≤ 8 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 8 := Real.rpow_one 8
    rw [show 1 / 2 * (1 - σ) = (1 - σ) / 2 by ring]
    exact div_le_div_of_nonneg_right this (Real.rpow_nonneg hs.le _)
  -- the number of planks
  have hX : 2 * (Real.sqrt s + (4 * ((H + 2 * δ) / θ + 2 * δ) + H)) / Real.sqrt s + 2 ≤ 16 / θ := by
    have h1 : H + 2 * δ ≤ 9 / 8 * Real.sqrt s := by nlinarith
    have h2 : (H + 2 * δ) / θ ≤ 9 / 8 * Real.sqrt s / θ := div_le_div_of_nonneg_right h1 hθ.le
    have h3 : Real.sqrt s ≤ Real.sqrt s / θ := by
      rw [le_div_iff₀ hθ]; nlinarith
    have h4 : 8 * δ ≤ Real.sqrt s / 2 := by nlinarith
    have hD : 4 * ((H + 2 * δ) / θ + 2 * δ) + H ≤ 6 * Real.sqrt s / θ := by
      have : 9 / 8 * Real.sqrt s / θ * 4 = 9 / 2 * (Real.sqrt s / θ) := by ring
      have e : 6 * Real.sqrt s / θ = 6 * (Real.sqrt s / θ) := by ring
      nlinarith
    have h5 : 2 * (Real.sqrt s + (4 * ((H + 2 * δ) / θ + 2 * δ) + H)) / Real.sqrt s ≤ 14 / θ := by
      rw [div_le_iff₀ hsp]
      have e14 : 14 / θ * Real.sqrt s = 14 * (Real.sqrt s / θ) := by ring
      have e6 : 6 * Real.sqrt s / θ = 6 * (Real.sqrt s / θ) := by ring
      rw [e6] at hD
      rw [e14]
      linarith
    have h6 : 2 ≤ 2 / θ := by rw [le_div_iff₀ hθ]; nlinarith
    have : 14 / θ + 2 / θ = 16 / θ := by ring
    linarith
  have hpos1 : 0 ≤ K * (8 / Real.sqrt s) ^ (1 - σ) :=
    mul_nonneg hK (Real.rpow_nonneg (by positivity) _)
  have hsσ : 0 < s ^ ((1 - σ) / 2) := Real.rpow_pos_of_pos hs _
  calc 10 * (K * (8 / Real.sqrt s) ^ (1 - σ)) *
        (2 * (Real.sqrt s + (4 * ((H + 2 * δ) / θ + 2 * δ) + H)) / Real.sqrt s + 2)
      ≤ 10 * (K * (8 / s ^ ((1 - σ) / 2))) * (16 / θ) := by
        gcongr
    _ = 1280 * K / θ / s ^ ((1 - σ) / 2) := by field_simp; ring

/-- The heavy windows satisfy the volume hypothesis of the window lemma. -/
theorem hvol_of_heavy {σ δ s θ K ε₁ ηl N PB L n M Mw : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hδ : 0 < δ) (hδs : δ ≤ s) (hθ : 0 < θ) (hK : 0 < K) (hε₁ : 0 < ε₁) (hn : 0 < n)
    (hN : 0 < N) (hNle : N ≤ 2048 * s ^ (2 - σ - ε₁) * δ ^ (-ε₁) * n)
    (hPB : 0 < PB) (hPBle : PB ≤ 1280 * K / θ / s ^ ((1 - σ) / 2))
    (hL : 0 < L) (hLle : L ≤ 1 / Real.sqrt s)
    (hM : δ ^ ε₁ * n * δ ^ 2 ≤ M) (hMw : Real.sqrt s * M / 60 ≤ Mw)
    (hkey : 3600 / 9 * (16 * 2304 * 2048 * 1280) * K * θ⁻¹ ^ 5 * δ ^ (-(3 * ε₁)) *
      s ^ (ηl - ε₁) ≤ 1) :
    s ^ (1 + σ / 2 + ηl) ≤ 9 * s * θ ^ 4 * Mw ^ 2 / (16 * 2304 * N * δ ^ 4 * PB * L * n) := by
  have hs : 0 < s := hδ.trans_le hδs
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hMw0 : 0 ≤ Mw := le_trans (by positivity) hMw
  rw [le_div_iff₀ (by positivity)]
  -- the mass of the window
  have hMw2 : s * (δ ^ ε₁ * n * δ ^ 2) ^ 2 / 3600 ≤ Mw ^ 2 := by
    have h1 : Real.sqrt s * (δ ^ ε₁ * n * δ ^ 2) / 60 ≤ Mw := by
      refine le_trans ?_ hMw
      gcongr
    have h2 : 0 ≤ Real.sqrt s * (δ ^ ε₁ * n * δ ^ 2) / 60 := by positivity
    have h3 := pow_le_pow_left₀ h2 h1 2
    calc s * (δ ^ ε₁ * n * δ ^ 2) ^ 2 / 3600 = (Real.sqrt s * (δ ^ ε₁ * n * δ ^ 2) / 60) ^ 2 := by
          have hsq2 : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
          rw [div_pow, mul_pow (Real.sqrt s) (δ ^ ε₁ * n * δ ^ 2) 2, hsq2]; ring
      _ ≤ Mw ^ 2 := h3
  -- the denominator
  set Nb := 2048 * s ^ (2 - σ - ε₁) * δ ^ (-ε₁) * n
  set Pb := 1280 * K / θ / s ^ ((1 - σ) / 2)
  have hden : 16 * 2304 * N * δ ^ 4 * PB * L * n ≤
      16 * 2304 * Nb * δ ^ 4 * Pb * (1 / Real.sqrt s) * n := by
    gcongr
  -- powers of `s`
  set A := δ ^ ε₁ with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos hδ _
  have hAneg : δ ^ (-ε₁) = A⁻¹ := Real.rpow_neg hδ.le ε₁
  have hA3 : δ ^ (-(3 * ε₁)) = (A ^ 3)⁻¹ := by
    rw [Real.rpow_neg hδ.le, mul_comm, Real.rpow_mul hδ.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  set T := s ^ (1 + σ / 2 + ηl) * s ^ (2 - σ - ε₁) / s ^ ((1 - σ) / 2) / Real.sqrt s with hT
  have hTe : T = s ^ 2 * s ^ (ηl - ε₁) := by
    rw [hT, Real.sqrt_eq_rpow, ← Real.rpow_add hs, ← Real.rpow_sub hs, ← Real.rpow_sub hs,
      ← Real.rpow_two, ← Real.rpow_add hs]
    congr 1; ring
  have hsη : 0 ≤ s ^ (ηl - ε₁) := Real.rpow_nonneg hs.le _
  have hsa : 0 < s ^ (1 + σ / 2 + ηl) := Real.rpow_pos_of_pos hs _
  have hsb : 0 < s ^ ((1 - σ) / 2) := Real.rpow_pos_of_pos hs _
  have hsc : 0 < s ^ (2 - σ - ε₁) := Real.rpow_pos_of_pos hs _
  -- the key inequality without negative powers
  have hkey' : 3600 / 9 * (16 * 2304 * 2048 * 1280) * K * s ^ (ηl - ε₁) ≤ θ ^ 5 * A ^ 3 := by
    rw [hA3, inv_pow] at hkey
    have h5 : 0 < θ ^ 5 * A ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_right hkey h5.le
    rw [one_mul] at this
    calc 3600 / 9 * (16 * 2304 * 2048 * 1280) * K * s ^ (ηl - ε₁)
        = 3600 / 9 * (16 * 2304 * 2048 * 1280) * K * (θ ^ 5)⁻¹ * (A ^ 3)⁻¹ * s ^ (ηl - ε₁) *
          (θ ^ 5 * A ^ 3) := by field_simp
      _ ≤ θ ^ 5 * A ^ 3 := this
  calc s ^ (1 + σ / 2 + ηl) * (16 * 2304 * N * δ ^ 4 * PB * L * n)
      ≤ s ^ (1 + σ / 2 + ηl) * (16 * 2304 * Nb * δ ^ 4 * Pb * (1 / Real.sqrt s) * n) :=
        mul_le_mul_of_nonneg_left hden hsa.le
    _ = 16 * 2304 * 2048 * 1280 * K / θ * n ^ 2 * δ ^ 4 / A * T := by
        rw [hT]; simp only [Nb, Pb, hAneg]; field_simp
    _ = 16 * 2304 * 2048 * 1280 * K / θ * n ^ 2 * δ ^ 4 / A * (s ^ 2 * s ^ (ηl - ε₁)) := by
        rw [hTe]
    _ ≤ 9 / 3600 * s ^ 2 * θ ^ 4 * n ^ 2 * δ ^ 4 * A ^ 2 := by
        have e : 16 * 2304 * 2048 * 1280 * K / θ * n ^ 2 * δ ^ 4 / A * (s ^ 2 * s ^ (ηl - ε₁)) =
            9 / 3600 * s ^ 2 * n ^ 2 * δ ^ 4 / (θ * A) *
              (3600 / 9 * (16 * 2304 * 2048 * 1280) * K * s ^ (ηl - ε₁)) := by
          field_simp
        rw [e]
        calc 9 / 3600 * s ^ 2 * n ^ 2 * δ ^ 4 / (θ * A) *
              (3600 / 9 * (16 * 2304 * 2048 * 1280) * K * s ^ (ηl - ε₁))
            ≤ 9 / 3600 * s ^ 2 * n ^ 2 * δ ^ 4 / (θ * A) * (θ ^ 5 * A ^ 3) :=
              mul_le_mul_of_nonneg_left hkey' (by positivity)
          _ = 9 / 3600 * s ^ 2 * θ ^ 4 * n ^ 2 * δ ^ 4 * A ^ 2 := by field_simp
    _ = 9 * s * θ ^ 4 * (s * (A * n * δ ^ 2) ^ 2 / 3600) := by ring
    _ ≤ 9 * s * θ ^ 4 * Mw ^ 2 := by gcongr

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
