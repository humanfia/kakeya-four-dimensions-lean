-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GGCore

/-!
# Numerics of the global grains

The conditions `GGNum` at a level radius `ρ0 ∈ [ρc/16, ρc]`, `ρc ∈ [τ^θ, τ^(θ-εT)]`, follow
from finitely many conditions `τ ^ p ≤ k` with `p > 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal

/-- The scales of the rescaled fibre. -/
theorem gg_scales {τ θ εT ρc ρ0 : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hρclo : τ ^ θ ≤ ρc) (hρchi : ρc ≤ τ ^ (θ - εT)) (hρ0lo : ρc / 16 ≤ ρ0) (hρ0hi : ρ0 ≤ ρc) :
    τ ^ θ / 16 ≤ ρ0 ∧ ρ0 ≤ τ ^ (θ - εT) ∧
      bR * (1 / 100 / ρ0) * τ ≤ τ ^ (1 - θ) ∧
      τ ^ (1 - θ + εT) / 200 ≤ bR * (1 / 100 / ρ0) * τ := by
  have hθpos : 0 < τ ^ θ := Real.rpow_pos_of_pos hτ θ
  have hρ0 : 0 < ρ0 := by linarith
  have hb1 := bR_le_one
  have hb2 := half_le_bR
  refine ⟨by linarith, hρ0hi.trans hρchi, ?_, ?_⟩
  · have h1 : bR * (1 / 100 / ρ0) * τ ≤ 1 * (1 / 100 / ρ0) * τ := by
      gcongr
    have h2 : (1 / 100 / ρ0) * τ ≤ 16 / 100 * (τ / τ ^ θ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hρ0]
      have : 16 / 100 * (τ / τ ^ θ) * ρ0 ≥ 16 / 100 * (τ / τ ^ θ) * (τ ^ θ / 16) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e : 16 / 100 * (τ / τ ^ θ) * (τ ^ θ / 16) = 1 / 100 * τ := by field_simp
      linarith
    have h3 : τ / τ ^ θ = τ ^ (1 - θ) := by
      rw [Real.rpow_sub hτ, Real.rpow_one]
    rw [h3] at h2
    have h4 : 0 ≤ τ ^ (1 - θ) := by positivity
    linarith
  · have h1 : 1 / 2 * (1 / 100 / ρ0) * τ ≤ bR * (1 / 100 / ρ0) * τ := by gcongr
    have h2 : τ ^ (1 - θ + εT) / 200 ≤ 1 / 2 * (1 / 100 / ρ0) * τ := by
      have hρ0' : ρ0 ≤ τ ^ (θ - εT) := hρ0hi.trans hρchi
      have hpos : 0 < τ ^ (θ - εT) := Real.rpow_pos_of_pos hτ _
      have e : τ ^ (1 - θ + εT) = τ / τ ^ (θ - εT) := by
        have h1 : τ ^ (1 - θ + εT) = τ ^ ((1 : ℝ) - (θ - εT)) := by congr 1; ring
        rw [h1, Real.rpow_sub hτ, Real.rpow_one]
      rw [e]
      have : τ / τ ^ (θ - εT) ≤ τ / ρ0 := div_le_div_of_nonneg_left hτ.le hρ0 hρ0'
      have e2 : 1 / 2 * (1 / 100 / ρ0) * τ = τ / ρ0 / 200 := by field_simp; norm_num
      rw [e2]
      linarith
    linarith

/-- The mass condition of the fibre rescaling. -/
theorem gg_Fmass {τ θ εF εT τ' C1 N0 : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hεT : 0 ≤ εT)
    (hεF : 0 < εF) (hC1 : 0 < C1) (hN0 : 0 ≤ N0) (hτ'0 : 0 < τ') (hτ' : τ' ≤ τ ^ (1 - θ))
    (hc : τ ^ ((1 - θ) * εF - 2 * εT) ≤ 1 / (2 * C1 * (1 + 384 * 2312 * 10 ^ 4 * N0))) :
    τ' ^ εF ≤ bR * (τ ^ εT / C1 - 384 * (2312 * τ ^ (-εT) / (1 / 100) ^ 2 * τ' ^ εF) * N0) := by
  have hb1 := bR_le_one
  have hb2 := half_le_bR
  have hP : τ' ^ εF ≤ τ ^ ((1 - θ) * εF) := rpow_le_of_le_rpow hτ hτ'0.le hτ' hεF.le
  have hP0 : 0 ≤ τ' ^ εF := by positivity
  set K0 : ℝ := 384 * 2312 * 10 ^ 4 * N0 with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hinv : 1 ≤ τ ^ (-εT) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by linarith)
  have hT : τ ^ εT * τ ^ (-εT) = 1 := by rw [← Real.rpow_add hτ]; simp
  -- `τ ^ ((1 - θ) εF - εT) = τ ^ ((1 - θ) εF - 2 εT) * τ ^ εT`
  have hsplit : τ ^ ((1 - θ) * εF) * τ ^ (-εT) =
      τ ^ ((1 - θ) * εF - 2 * εT) * τ ^ εT := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ]; congr 1; ring
  have h1 : τ' ^ εF * (1 + bR * K0 * τ ^ (-εT)) ≤ τ ^ ((1 - θ) * εF) * ((1 + K0) * τ ^ (-εT)) := by
    apply mul_le_mul hP _ (by positivity) (by positivity)
    have a : bR * K0 * τ ^ (-εT) ≤ K0 * τ ^ (-εT) :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hK00 hb1) (by positivity)
    calc 1 + bR * K0 * τ ^ (-εT) ≤ τ ^ (-εT) + K0 * τ ^ (-εT) := by linarith
      _ = (1 + K0) * τ ^ (-εT) := by ring
  have h2 : τ ^ ((1 - θ) * εF) * ((1 + K0) * τ ^ (-εT)) ≤ τ ^ εT / (2 * C1) := by
    have h3 : τ ^ ((1 - θ) * εF) * ((1 + K0) * τ ^ (-εT)) =
        (1 + K0) * (τ ^ ((1 - θ) * εF - 2 * εT) * τ ^ εT) := by rw [← hsplit]; ring
    rw [h3]
    have h4 : (1 + K0) * τ ^ ((1 - θ) * εF - 2 * εT) ≤ 1 / (2 * C1) := by
      calc (1 + K0) * τ ^ ((1 - θ) * εF - 2 * εT) ≤ (1 + K0) * (1 / (2 * C1 * (1 + K0))) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ = 1 / (2 * C1) := by field_simp
    have h5 : 0 ≤ τ ^ εT := by positivity
    calc (1 + K0) * (τ ^ ((1 - θ) * εF - 2 * εT) * τ ^ εT)
        = ((1 + K0) * τ ^ ((1 - θ) * εF - 2 * εT)) * τ ^ εT := by ring
      _ ≤ 1 / (2 * C1) * τ ^ εT := mul_le_mul_of_nonneg_right h4 h5
      _ = τ ^ εT / (2 * C1) := by ring
  have h6 : τ ^ εT / (2 * C1) ≤ bR * (τ ^ εT / C1) := by
    have e : τ ^ εT / (2 * C1) = 1 / 2 * (τ ^ εT / C1) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hb2 (by positivity)
  have e : bR * (τ ^ εT / C1 - 384 * (2312 * τ ^ (-εT) / (1 / 100) ^ 2 * τ' ^ εF) * N0) =
      bR * (τ ^ εT / C1) - τ' ^ εF * (bR * K0 * τ ^ (-εT)) := by rw [hK0]; ring
  rw [e]
  nlinarith

/-- The volume condition of the fibre rescaling. -/
theorem gg_Fvol {σ τ θ εF εT ε1 tF ρc ρ0 : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hθ0 : 0 < θ)
    (hσ1 : σ ≤ 1) (hεF : 0 < εF) (hεFσ : εF ≤ σ) (htF : tF = σ + εF / 4)
    (hρclo : τ ^ θ ≤ ρc) (hρc1 : ρc ≤ 1) (hρ0lo : ρc / 16 ≤ ρ0) (hρ0hi : ρ0 ≤ ρc)
    (hc : τ ^ ((1 - θ) * εF - θ * (εF / 4) - εT - ε1) ≤ 1 / 15730) :
    bR ^ 3 * (1 / 100 / ρ0) ^ 2 * (3072 * ρc ^ 2 * τ ^ (-εT) * τ ^ (σ - ε1)) ≤
      ρc ^ tF * (bR * (1 / 100 / ρ0) * τ) ^ (σ - εF) := by
  have hb1 := bR_le_one
  have hb2 := half_le_bR
  have hb0 := bR_pos
  have hρc0 : 0 < ρc := lt_of_lt_of_le (Real.rpow_pos_of_pos hτ θ) hρclo
  have hρ0 : 0 < ρ0 := by linarith
  -- the left side
  have hL : bR ^ 3 * (1 / 100 / ρ0) ^ 2 * (3072 * ρc ^ 2 * τ ^ (-εT) * τ ^ (σ - ε1)) ≤
      78.6432 * τ ^ (σ - εT - ε1) := by
    have h1 : (1 / 100 / ρ0) ^ 2 * ρc ^ 2 ≤ 256 / 10000 := by
      have h2 : 1 / 100 / ρ0 * ρc ≤ 16 / 100 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hρ0]; linarith
      have h3 : 0 ≤ 1 / 100 / ρ0 * ρc := by positivity
      have h4 := pow_le_pow_left₀ h3 h2 2
      rw [mul_pow] at h4
      calc (1 / 100 / ρ0) ^ 2 * ρc ^ 2 ≤ (16 / 100) ^ 2 := h4
        _ = 256 / 10000 := by norm_num
    have h3 : bR ^ 3 ≤ 1 := pow_le_one₀ hb0.le hb1
    have e : τ ^ (-εT) * τ ^ (σ - ε1) = τ ^ (σ - εT - ε1) := by
      rw [← Real.rpow_add hτ]; congr 1; ring
    have h4 : 0 ≤ τ ^ (σ - εT - ε1) := by positivity
    calc bR ^ 3 * (1 / 100 / ρ0) ^ 2 * (3072 * ρc ^ 2 * τ ^ (-εT) * τ ^ (σ - ε1))
        = bR ^ 3 * ((1 / 100 / ρ0) ^ 2 * ρc ^ 2) * 3072 * (τ ^ (-εT) * τ ^ (σ - ε1)) := by ring
      _ ≤ 1 * (256 / 10000) * 3072 * (τ ^ (-εT) * τ ^ (σ - ε1)) := by gcongr
      _ = 78.6432 * τ ^ (σ - εT - ε1) := by rw [e]; norm_num
  -- the right side
  have hτ' : τ / (200 * ρc) ≤ bR * (1 / 100 / ρ0) * τ := by
    have : 1 / 2 * (1 / 100 / ρc) * τ ≤ bR * (1 / 100 / ρ0) * τ := by
      gcongr
    calc τ / (200 * ρc) = 1 / 2 * (1 / 100 / ρc) * τ := by field_simp; norm_num
      _ ≤ _ := this
  have hR1 : (τ / (200 * ρc)) ^ (σ - εF) ≤ (bR * (1 / 100 / ρ0) * τ) ^ (σ - εF) :=
    Real.rpow_le_rpow (by positivity) hτ' (by linarith)
  have hR2 : ρc ^ tF * (τ / (200 * ρc)) ^ (σ - εF) =
      τ ^ (σ - εF) * ρc ^ (εF / 4 + εF) * 200 ^ (-(σ - εF)) := by
    rw [Real.div_rpow hτ.le (by positivity), Real.mul_rpow (by norm_num) hρc0.le, htF]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 200)]
    have : ρc ^ (σ + εF / 4) = ρc ^ (σ - εF) * ρc ^ (εF / 4 + εF) := by
      rw [← Real.rpow_add hρc0]; congr 1; ring
    rw [this]
    have h1 : 0 < ρc ^ (σ - εF) := Real.rpow_pos_of_pos hρc0 _
    have h2 : 0 < (200 : ℝ) ^ (σ - εF) := by positivity
    field_simp
  have hR3 : τ ^ (θ * (εF / 4 + εF)) ≤ ρc ^ (εF / 4 + εF) := by
    rw [Real.rpow_mul hτ.le]
    exact Real.rpow_le_rpow (by positivity) hρclo (by positivity)
  have hR4 : (1 : ℝ) / 200 ≤ 200 ^ (-(σ - εF)) := by
    rw [Real.rpow_neg (by norm_num), one_div]
    apply inv_anti₀ (by positivity)
    calc (200 : ℝ) ^ (σ - εF) ≤ 200 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 200 := Real.rpow_one 200
  -- combine
  have hsplit : τ ^ (σ - εT - ε1) =
      τ ^ ((1 - θ) * εF - θ * (εF / 4) - εT - ε1) * (τ ^ (σ - εF) * τ ^ (θ * (εF / 4 + εF))) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ]; congr 1; ring
  have hpos1 : 0 ≤ τ ^ (σ - εF) * τ ^ (θ * (εF / 4 + εF)) := by positivity
  calc bR ^ 3 * (1 / 100 / ρ0) ^ 2 * (3072 * ρc ^ 2 * τ ^ (-εT) * τ ^ (σ - ε1))
      ≤ 78.6432 * τ ^ (σ - εT - ε1) := hL
    _ = 78.6432 * τ ^ ((1 - θ) * εF - θ * (εF / 4) - εT - ε1) *
          (τ ^ (σ - εF) * τ ^ (θ * (εF / 4 + εF))) := by rw [hsplit]; ring
    _ ≤ 78.6432 * (1 / 15730) * (τ ^ (σ - εF) * τ ^ (θ * (εF / 4 + εF))) := by gcongr
    _ ≤ τ ^ (σ - εF) * ρc ^ (εF / 4 + εF) * 200 ^ (-(σ - εF)) := by
        have h5 : 0 ≤ τ ^ (σ - εF) := by positivity
        have h6 := mul_le_mul_of_nonneg_left hR3 h5
        have h7 : 0 ≤ τ ^ (σ - εF) * ρc ^ (εF / 4 + εF) := by positivity
        have h8 := mul_le_mul_of_nonneg_left hR4 h7
        nlinarith
    _ = ρc ^ tF * (τ / (200 * ρc)) ^ (σ - εF) := hR2.symm
    _ ≤ ρc ^ tF * (bR * (1 / 100 / ρ0) * τ) ^ (σ - εF) := by
        gcongr

/-- The conditions on the number of slabs of a block. -/
theorem gg_N {τ ε1 ρ0 : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε1 : 0 ≤ ε1) (hτρ0 : τ ≤ ρ0)
    (hLρ : τ ^ (-ε1) * ρ0 ≤ 1 / 320) :
    1 ≤ ⌊1 / (64 * τ ^ (-ε1) * ρ0)⌋₊ ∧
      (⌊1 / (64 * τ ^ (-ε1) * ρ0)⌋₊ : ℝ) * (bR * ρ0) ≤ 1 ∧
      8 * τ ^ (-ε1) * (2 * (ρ0 * (⌊1 / (64 * τ ^ (-ε1) * ρ0)⌋₊ + 2)) + 6 * τ) ≤ 1 / 2 ∧
      1 / (128 * τ ^ (-ε1) * ρ0) ≤ (⌊1 / (64 * τ ^ (-ε1) * ρ0)⌋₊ : ℝ) := by
  have hρ0 : 0 < ρ0 := lt_of_lt_of_le hτ hτρ0
  have hL1 : 1 ≤ τ ^ (-ε1) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by linarith)
  set L := τ ^ (-ε1) with hL
  have hLρ0 : 0 < L * ρ0 := by positivity
  set x : ℝ := 1 / (64 * L * ρ0) with hx
  have hx5 : 5 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]; nlinarith
  have hfl := Nat.floor_le (show (0 : ℝ) ≤ x by linarith)
  have hfl2 := Nat.lt_floor_add_one x
  have hb1 := bR_le_one
  have hb0 := bR_pos
  refine ⟨Nat.le_floor (by norm_num; linarith), ?_, ?_, ?_⟩
  · calc (⌊x⌋₊ : ℝ) * (bR * ρ0) ≤ x * (1 * ρ0) := by gcongr
      _ = 1 / (64 * L) := by rw [hx]; field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  · have h1 : (⌊x⌋₊ : ℝ) * (L * ρ0) ≤ 1 / 64 := by
      calc (⌊x⌋₊ : ℝ) * (L * ρ0) ≤ x * (L * ρ0) := by gcongr
        _ = 1 / 64 := by rw [hx]; field_simp
    have h2 : L * τ ≤ L * ρ0 := mul_le_mul_of_nonneg_left hτρ0 (by linarith)
    nlinarith
  · have h1 : x / 2 ≤ x - 1 := by linarith
    have h2 : 1 / (128 * L * ρ0) = x / 2 := by rw [hx]; field_simp; ring
    rw [h2]; linarith

/-- The mass condition of the restricted rescaled fibre. -/
theorem gg_massN {τ θ η2 εF ε1 ρ0 τ' Nr : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hθ1 : θ ≤ 1)
    (hρ0 : 0 < ρ0) (hτ'0 : 0 < τ') (hτ' : τ' ≤ τ ^ (1 - θ)) (h2F : 2 * εF ≤ η2)
    (hN : 1 / (128 * τ ^ (-ε1) * ρ0) ≤ Nr)
    (hc : τ ^ ((1 - θ) * (η2 - 2 * εF) - ε1) ≤ 1 / 20873216) :
    τ' ^ η2 ≤ Nr * (bR * ρ0) / 7 * (τ' ^ εF * τ' ^ εF / 11648) := by
  have hb2 := half_le_bR
  have hL : 0 < τ ^ (-ε1) := by positivity
  have hNr : τ ^ ε1 / 1792 ≤ Nr * (bR * ρ0) / 7 := by
    have h1 : 1 / (128 * τ ^ (-ε1) * ρ0) * (1 / 2 * ρ0) / 7 ≤ Nr * (bR * ρ0) / 7 := by
      gcongr
      exact (div_pos one_pos (by positivity)).le.trans hN
    have h2 : 1 / (128 * τ ^ (-ε1) * ρ0) * (1 / 2 * ρ0) / 7 = τ ^ ε1 / 1792 := by
      rw [Real.rpow_neg hτ.le]; field_simp; ring
    linarith
  have hsq : τ' ^ εF * τ' ^ εF = τ' ^ (2 * εF) := by rw [← Real.rpow_add hτ'0]; ring_nf
  rw [hsq]
  have hsplit : τ' ^ η2 = τ' ^ (2 * εF) * τ' ^ (η2 - 2 * εF) := by
    rw [← Real.rpow_add hτ'0]; congr 1; ring
  have h3 : τ' ^ (η2 - 2 * εF) ≤ τ ^ ((1 - θ) * (η2 - 2 * εF)) :=
    rpow_le_of_le_rpow hτ hτ'0.le hτ' (by linarith)
  have h4 : τ ^ ((1 - θ) * (η2 - 2 * εF)) = τ ^ ε1 * τ ^ ((1 - θ) * (η2 - 2 * εF) - ε1) := by
    rw [← Real.rpow_add hτ]; congr 1; ring
  have h5 : 0 ≤ τ' ^ (2 * εF) := by positivity
  have h6 : 0 ≤ τ ^ ε1 := by positivity
  rw [hsplit]
  calc τ' ^ (2 * εF) * τ' ^ (η2 - 2 * εF) ≤ τ' ^ (2 * εF) * (τ ^ ε1 * (1 / 20873216)) := by
        apply mul_le_mul_of_nonneg_left _ h5
        calc τ' ^ (η2 - 2 * εF) ≤ τ ^ ((1 - θ) * (η2 - 2 * εF)) := h3
          _ = τ ^ ε1 * τ ^ ((1 - θ) * (η2 - 2 * εF) - ε1) := h4
          _ ≤ τ ^ ε1 * (1 / 20873216) := mul_le_mul_of_nonneg_left hc h6
    _ = τ ^ ε1 / 1792 * (τ' ^ (2 * εF) / 11648) := by ring
    _ ≤ Nr * (bR * ρ0) / 7 * (τ' ^ (2 * εF) / 11648) := by gcongr

/-- The conditions at the final scale `δf ∈ [τ'^c, τ'^(c - ε2)]`. -/
theorem gg_fin {σ ε e c θ ε2 εT ε1 τ ρ0 τ' d0 : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hσ0 : 0 ≤ σ) (he : 0 < e) (heε : e ≤ ε) (hc : 0 < c) (hc1 : c ≤ 1)
    (hθ : (1 - θ) * c = θ) (hθ2 : θ ≤ 1 / 2) (hε2 : 0 ≤ ε2) (hε2c : ε2 ≤ c / 2)
    (hεT : 0 ≤ εT)
    (hρ0lo : τ ^ θ / 16 ≤ ρ0) (hρ0hi : ρ0 ≤ τ ^ (θ - εT))
    (hτ'lo : τ ^ (1 - θ + εT) / 200 ≤ τ') (hτ'hi : τ' ≤ τ ^ (1 - θ))
    (c8 : τ ^ (c * e / 32 - 2 * εT) ≤ 1 / 200) (c9 : τ ^ (c * e / 32 - ε2) ≤ 1 / 32)
    (c10 : τ ^ (c * e / 32 - ε1) ≤ 1 / 1280) (c11 : τ ^ (5 * (c * e / 32) - ε1) ≤ 1 / 83200)
    (c12 : τ ^ (c / 4) ≤ d0) :
    ∀ δf : ℝ, τ' ^ c ≤ δf → δf ≤ τ' ^ (c - ε2) →
      bR * ρ0 ≤ δf ^ (-(ε / 8)) * δf ∧ δf ≤ δf ^ (-(ε / 8)) * (bR * ρ0) ∧
      1280 * τ ^ (-ε1) ≤ δf ^ (-(ε / 8)) ∧
      20800 * (δf ^ (-(ε / 8))) ^ 3 * (4 ^ (1 - σ) * τ ^ (-ε1)) ≤ δf ^ (-ε) ∧ δf ≤ d0 ∧
      1280 * τ ^ (-ε1) ≤ δf ^ (-ε) := by
  intro δf hδlo hδhi
  have hb1 := bR_le_one
  have hb2 := half_le_bR
  have hτ'0 : 0 < τ' := lt_of_lt_of_le (by positivity) hτ'lo
  have hδf : 0 < δf := lt_of_lt_of_le (Real.rpow_pos_of_pos hτ'0 c) hδlo
  have hτ'1 : τ' ≤ 1 := hτ'hi.trans (Real.rpow_le_one hτ.le hτ1 (by linarith))
  -- `δf ≤ τ ^ (θ - (1 - θ) ε2) ≤ τ ^ (c / 4)`
  have hδup : δf ≤ τ ^ ((1 - θ) * (c - ε2)) :=
    hδhi.trans (rpow_le_of_le_rpow hτ hτ'0.le hτ'hi (by linarith))
  have hδc4 : δf ≤ τ ^ (c / 4) :=
    hδup.trans (Real.rpow_le_rpow_of_exponent_ge hτ hτ1 (by nlinarith))
  have hδf1 : δf ≤ 1 := hδc4.trans (Real.rpow_le_one hτ.le hτ1 (by positivity))
  -- the constant `K = δf ^ (-ε/8)` is large
  set K := δf ^ (-(ε / 8)) with hK
  have hKe : τ ^ (-(c * e / 32)) ≤ K := by
    calc τ ^ (-(c * e / 32)) = (τ ^ (c / 4)) ^ (-(e / 8)) := by
          rw [← Real.rpow_mul hτ.le]; congr 1; ring
      _ ≤ δf ^ (-(e / 8)) := Real.rpow_le_rpow_of_nonpos hδf hδc4 (by linarith)
      _ ≤ K := Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by linarith)
  have hK1 : 1 ≤ K := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδf hδf1 (by linarith)
  have hK8 : δf ^ (-ε) = K ^ 8 := by
    rw [hK, ← Real.rpow_natCast, ← Real.rpow_mul hδf.le]; congr 1; push_cast; ring
  -- `δf ≥ τ ^ (θ + εT) / 200`
  have hδlow : τ ^ (θ + εT) / 200 ≤ δf := by
    have h1 : (τ ^ (1 - θ + εT) / 200) ^ c ≤ τ' ^ c := Real.rpow_le_rpow (by positivity) hτ'lo hc.le
    have h2 : (τ ^ (1 - θ + εT) / 200) ^ c = τ ^ (c * (1 - θ + εT)) / 200 ^ c := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hτ.le, mul_comm]
    have h3 : τ ^ (θ + εT) ≤ τ ^ (c * (1 - θ + εT)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hτ hτ1
      nlinarith
    have h4 : (200 : ℝ) ^ c ≤ 200 := by
      calc (200 : ℝ) ^ c ≤ 200 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc1
        _ = 200 := Real.rpow_one 200
    have h5 : τ ^ (θ + εT) / 200 ≤ τ ^ (c * (1 - θ + εT)) / 200 ^ c := by
      apply div_le_div₀ (by positivity) h3 (by positivity) h4
    linarith
  have hρ0pos : 0 < ρ0 := lt_of_lt_of_le (by positivity) hρ0lo
  refine ⟨?_, ?_, ?_, ?_, hδc4.trans c12, ?_⟩
  · -- `bR ρ0 ≤ K δf`
    have h1 : bR * ρ0 ≤ τ ^ (θ - εT) := (mul_le_of_le_one_left hρ0pos.le hb1).trans hρ0hi
    have h2 : τ ^ (θ - εT) = τ ^ (c * e / 32 - 2 * εT) * (τ ^ (-(c * e / 32)) * τ ^ (θ + εT)) := by
      rw [← Real.rpow_add hτ, ← Real.rpow_add hτ]; congr 1; ring
    have h3 : 0 ≤ τ ^ (-(c * e / 32)) * τ ^ (θ + εT) := by positivity
    calc bR * ρ0 ≤ τ ^ (θ - εT) := h1
      _ = τ ^ (c * e / 32 - 2 * εT) * (τ ^ (-(c * e / 32)) * τ ^ (θ + εT)) := h2
      _ ≤ 1 / 200 * (τ ^ (-(c * e / 32)) * τ ^ (θ + εT)) := mul_le_mul_of_nonneg_right c8 h3
      _ = τ ^ (-(c * e / 32)) * (τ ^ (θ + εT) / 200) := by ring
      _ ≤ K * δf := mul_le_mul hKe hδlow (by positivity) (by positivity)
  · -- `δf ≤ K bR ρ0`
    have h1 : τ ^ θ / 32 ≤ bR * ρ0 := by
      calc τ ^ θ / 32 = 1 / 2 * (τ ^ θ / 16) := by ring
        _ ≤ bR * ρ0 := mul_le_mul hb2 hρ0lo (by positivity) (by positivity)
    have h2 : τ ^ ((1 - θ) * (c - ε2)) =
        τ ^ (c * e / 32 - (1 - θ) * ε2) * (τ ^ (-(c * e / 32)) * τ ^ θ) := by
      rw [← Real.rpow_add hτ, ← Real.rpow_add hτ]; congr 1; nlinarith [hθ]
    have h3 : τ ^ (c * e / 32 - (1 - θ) * ε2) ≤ 1 / 32 :=
      (Real.rpow_le_rpow_of_exponent_ge hτ hτ1 (by nlinarith)).trans c9
    have h4 : 0 ≤ τ ^ (-(c * e / 32)) * τ ^ θ := by positivity
    calc δf ≤ τ ^ ((1 - θ) * (c - ε2)) := hδup
      _ = τ ^ (c * e / 32 - (1 - θ) * ε2) * (τ ^ (-(c * e / 32)) * τ ^ θ) := h2
      _ ≤ 1 / 32 * (τ ^ (-(c * e / 32)) * τ ^ θ) := mul_le_mul_of_nonneg_right h3 h4
      _ = τ ^ (-(c * e / 32)) * (τ ^ θ / 32) := by ring
      _ ≤ K * (bR * ρ0) := mul_le_mul hKe h1 (by positivity) (by positivity)
  · -- `1280 τ ^ (-ε1) ≤ K`
    have h2 : τ ^ (-ε1) = τ ^ (c * e / 32 - ε1) * τ ^ (-(c * e / 32)) := by
      rw [← Real.rpow_add hτ]; congr 1; ring
    calc 1280 * τ ^ (-ε1) = 1280 * τ ^ (c * e / 32 - ε1) * τ ^ (-(c * e / 32)) := by
          rw [h2]; ring
      _ ≤ 1280 * (1 / 1280) * τ ^ (-(c * e / 32)) := by gcongr
      _ = τ ^ (-(c * e / 32)) := by ring
      _ ≤ K := hKe
  · -- the constant of the slices
    have h4 : (4 : ℝ) ^ (1 - σ) ≤ 4 := by
      calc (4 : ℝ) ^ (1 - σ) ≤ 4 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := Real.rpow_one 4
    have hK5 : τ ^ (-(5 * (c * e / 32))) ≤ K ^ 5 := by
      calc τ ^ (-(5 * (c * e / 32))) = (τ ^ (-(c * e / 32))) ^ 5 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le]; congr 1; push_cast; ring
        _ ≤ K ^ 5 := pow_le_pow_left₀ (by positivity) hKe 5
    have h2 : τ ^ (-ε1) = τ ^ (5 * (c * e / 32) - ε1) * τ ^ (-(5 * (c * e / 32))) := by
      rw [← Real.rpow_add hτ]; congr 1; ring
    have h5 : 20800 * (4 ^ (1 - σ) * τ ^ (-ε1)) ≤ K ^ 5 := by
      calc 20800 * (4 ^ (1 - σ) * τ ^ (-ε1)) ≤ 20800 * (4 * τ ^ (-ε1)) := by gcongr
        _ = 83200 * τ ^ (5 * (c * e / 32) - ε1) * τ ^ (-(5 * (c * e / 32))) := by rw [h2]; ring
        _ ≤ 83200 * (1 / 83200) * τ ^ (-(5 * (c * e / 32))) := by gcongr
        _ = τ ^ (-(5 * (c * e / 32))) := by ring
        _ ≤ K ^ 5 := hK5
    rw [hK8]
    have hK3 : 0 ≤ K ^ 3 := by positivity
    calc 20800 * K ^ 3 * (4 ^ (1 - σ) * τ ^ (-ε1)) = K ^ 3 * (20800 * (4 ^ (1 - σ) * τ ^ (-ε1))) := by
          ring
      _ ≤ K ^ 3 * K ^ 5 := mul_le_mul_of_nonneg_left h5 hK3
      _ = K ^ 8 := by ring
  · -- `1280 τ ^ (-ε1) ≤ δf ^ (-ε)`
    have h2 : τ ^ (-ε1) = τ ^ (c * e / 32 - ε1) * τ ^ (-(c * e / 32)) := by
      rw [← Real.rpow_add hτ]; congr 1; ring
    have h3 : 1280 * τ ^ (-ε1) ≤ K := by
      calc 1280 * τ ^ (-ε1) = 1280 * τ ^ (c * e / 32 - ε1) * τ ^ (-(c * e / 32)) := by
            rw [h2]; ring
        _ ≤ 1280 * (1 / 1280) * τ ^ (-(c * e / 32)) := by gcongr
        _ = τ ^ (-(c * e / 32)) := by ring
        _ ≤ K := hKe
    rw [hK8]
    have : K ≤ K ^ 8 := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ 8 := pow_le_pow_right₀ hK1 (by norm_num)
    linarith

/-- All numerical conditions of the global grains from the cutoffs. -/
theorem ggnum_of {σ ε e c θ ε2 η2 εF εT ε1 tF τ ρc ρ0 d0 τ'max : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 100) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (he : 0 < e) (heε : e ≤ ε) (hc : 0 < c) (hc1 : c ≤ 1)
    (hθ : (1 - θ) * c = θ) (hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hε2 : 0 ≤ ε2) (hε2c : ε2 ≤ c / 2) (hεT : 0 < εT) (hε1 : 0 ≤ ε1)
    (hεF : 0 < εF) (hεFσ : εF ≤ σ) (h2F : 2 * εF ≤ η2) (htF : tF = σ + εF / 4)
    (hρclo : τ ^ θ ≤ ρc) (hρchi : ρc ≤ τ ^ (θ - εT)) (hρ0lo : ρc / 16 ≤ ρ0) (hρ0hi : ρ0 ≤ ρc)
    (hτρ0 : τ ≤ ρ0)
    (c1 : τ ^ (θ - εT) ≤ 1 / 1000) (c2 : τ ^ (1 - 2 * θ) ≤ 25 / 256)
    (c3a : τ ^ (1 - θ) ≤ 1 / 10000000) (c3b : τ ^ (1 - θ) ≤ τ'max)
    (c4a : τ ^ ((1 - θ) * εF - 2 * εT) ≤ 1 / (34 * 10 ^ 7))
    (c4b : τ ^ ((1 - θ) * εF - 2 * εT) ≤ 1 / (2 * ((10 ^ 61 + 1 : ℕ) : ℝ) ^ (⌈εT⁻¹⌉₊ + 3) *
      (1 + 384 * 2312 * 10 ^ 4 * ((⌈εT⁻¹⌉₊ + 3 : ℕ) : ℝ))))
    (c5 : τ ^ ((1 - θ) * εF - θ * (εF / 4) - εT - ε1) ≤ 1 / 15730)
    (c6 : τ ^ (θ - εT - ε1) ≤ 1 / 320)
    (c7 : τ ^ ((1 - θ) * (η2 - 2 * εF) - ε1) ≤ 1 / 20873216)
    (c8 : τ ^ (c * e / 32 - 2 * εT) ≤ 1 / 200) (c9 : τ ^ (c * e / 32 - ε2) ≤ 1 / 32)
    (c10 : τ ^ (c * e / 32 - ε1) ≤ 1 / 1280) (c11 : τ ^ (5 * (c * e / 32) - ε1) ≤ 1 / 83200)
    (c12 : τ ^ (c / 4) ≤ d0) :
    GGNum σ ε c ε2 η2 εF εT ε1 tF τ ρc ρ0 d0 τ'max := by
  have hτ1' : τ ≤ 1 := hτ1.trans (by norm_num)
  obtain ⟨hρ0lo', hρ0hi', hτ'hi, hτ'lo⟩ := gg_scales hτ hτ1' hρclo hρchi hρ0lo hρ0hi
  have hρ0 : 0 < ρ0 := lt_of_lt_of_le hτ hτρ0
  have hτ'0 : 0 < bR * (1 / 100 / ρ0) * τ := by have := bR_pos; positivity
  have hρc1 : ρc ≤ 1 / 1000 := hρchi.trans c1
  -- the local grains scale
  have hloc1 : τ ≤ (5 * ρ0) ^ 2 := by
    have h1 : τ = τ ^ (1 - 2 * θ) * (τ ^ θ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le, ← Real.rpow_add hτ]
      push_cast; ring_nf; rw [Real.rpow_one]
    have h2 : (τ ^ θ) ^ 2 ≤ (16 * ρ0) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h3 : 0 ≤ τ ^ (1 - 2 * θ) := by positivity
    calc τ = τ ^ (1 - 2 * θ) * (τ ^ θ) ^ 2 := h1
      _ ≤ 25 / 256 * (16 * ρ0) ^ 2 := mul_le_mul c2 h2 (by positivity) (by norm_num)
      _ = (5 * ρ0) ^ 2 := by ring
  obtain ⟨hC2a, hC2b⟩ := cond_fibre hτ hτ'0 hτ'hi hεF c4a
  obtain ⟨hN1, hNh, hNL, hNlow⟩ := gg_N hτ hτ1' hε1 hτρ0 (by
    calc τ ^ (-ε1) * ρ0 ≤ τ ^ (-ε1) * τ ^ (θ - εT) := by gcongr
      _ = τ ^ (θ - εT - ε1) := by rw [← Real.rpow_add hτ]; congr 1; ring
      _ ≤ 1 / 320 := c6)
  refine ⟨hρc1, hloc1, ?_, hτ'hi.trans c3a, hC2a, hC2b, ?_, ?_, ?_, hτ'hi.trans c3b, hN1, hNh,
    hNL, ?_, ?_⟩
  · have : 5 * ρ0 ≤ 1 := by linarith
    nlinarith
  · exact gg_Fmass hτ hτ1' hεT.le hεF (by positivity) (by positivity) hτ'0 hτ'hi c4b
  · exact gg_Fvol hτ hτ1' hθ0 hσ1 hεF hεFσ htF hρclo (hρc1.trans (by norm_num)) hρ0lo hρ0hi c5
  · -- `τ' ≤ bR ρ0`
    have hb := bR_pos
    have h1 : (1 / 100 / ρ0) * τ ≤ ρ0 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hρ0]; nlinarith [hloc1]
    calc bR * (1 / 100 / ρ0) * τ = bR * ((1 / 100 / ρ0) * τ) := by ring
      _ ≤ bR * ρ0 := mul_le_mul_of_nonneg_left h1 hb.le
  · exact gg_massN hτ hτ1' (by linarith) hρ0 hτ'0 hτ'hi h2F hNlow c7
  · exact gg_fin hτ hτ1' hσ0 he heε hc hc1 hθ hθ2 hε2 hε2c hεT.le hρ0lo' hρ0hi' hτ'lo hτ'hi
      c8 c9 c10 c11 c12

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
