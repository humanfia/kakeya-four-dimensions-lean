-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.Weight.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.Basic
namespace WangZahlLot.Obl.wz_separated_scales_gain
theorem frostman_weight_identity {C L N r : ℝ} (hC : 0 < C) (hL : 0 < L) (hN : 0 < N) (hr : 0 < r) (σ : ℝ) :
    (C * L * N * r ^ 2)⁻¹ * (N * r ^ 2) *
      ((C * L * N * r ^ 2) ^ (-(3 / 2 : ℝ)) * L * (N * r)) ^ (-σ) =
      C ^ ((3 / 2 : ℝ) * σ - 1) * L ^ (σ / 2 - 1) * (N * r ^ 4) ^ (σ / 2) := by
  have hb : (C * L * N * r ^ 2) ^ (-(3 / 2 : ℝ)) * L * (N * r) =
      C ^ (-(3 / 2 : ℝ)) * L ^ (-(1 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) * r ^ (-2 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hN.le, Real.mul_rpow hC.le hL.le,
      ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    have hLp : L ^ (-(3 / 2 : ℝ)) * L = L ^ (-(1 / 2 : ℝ)) := by
      nth_rw 2 [← Real.rpow_one L]
      rw [← Real.rpow_add hL]
      norm_num
    have hNp : N ^ (-(3 / 2 : ℝ)) * N = N ^ (-(1 / 2 : ℝ)) := by
      nth_rw 2 [← Real.rpow_one N]
      rw [← Real.rpow_add hN]
      norm_num
    have hrp : r ^ ((2 : ℝ) * -(3 / 2)) * r = r ^ (-2 : ℝ) := by
      nth_rw 2 [← Real.rpow_one r]
      rw [← Real.rpow_add hr]
      norm_num
    calc
      _ = C ^ (-(3 / 2 : ℝ)) * (L ^ (-(3 / 2 : ℝ)) * L) *
          (N ^ (-(3 / 2 : ℝ)) * N) * (r ^ ((2 : ℝ) * -(3 / 2)) * r) := by ring
      _ = _ := by rw [hLp, hNp, hrp]
  rw [hb]
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hC.le, ← Real.rpow_mul hL.le, ← Real.rpow_mul hN.le, ← Real.rpow_mul hr.le]
  have hf : (C * L * N * r ^ 2)⁻¹ * (N * r ^ 2) = C⁻¹ * L⁻¹ := by field_simp
  rw [hf]
  have hCp : C⁻¹ * C ^ ((-(3 / 2 : ℝ)) * -σ) = C ^ ((3 / 2 : ℝ) * σ - 1) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hC]
    congr 1
    ring
  have hLp : L⁻¹ * L ^ ((-(1 / 2 : ℝ)) * -σ) = L ^ (σ / 2 - 1) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hL]
    congr 1
    ring
  have hNr : N ^ ((-(1 / 2 : ℝ)) * -σ) * r ^ ((-2 : ℝ) * -σ) =
      (N * r ^ 4) ^ (σ / 2) := by
    rw [Real.mul_rpow hN.le (by positivity), ← Real.rpow_natCast r 4, ← Real.rpow_mul hr.le]
    congr 2 <;> ring
  calc
    _ = (C⁻¹ * C ^ ((-(3 / 2 : ℝ)) * -σ)) * (L⁻¹ * L ^ ((-(1 / 2 : ℝ)) * -σ)) *
        (N ^ ((-(1 / 2 : ℝ)) * -σ) * r ^ ((-2 : ℝ) * -σ)) := by ring
    _ = _ := by rw [hCp, hLp, hNr]
/-- Only one power of the Frostman error is needed in this normalization. -/
theorem frostman_weight_lower {C L N r σ : ℝ} (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hN : 0 < N) (hr : 0 < r) (hσ : 0 ≤ σ) :
    C⁻¹ * L⁻¹ * (N * r ^ 4) ^ (σ / 2) ≤
      (C * L * N * r ^ 2)⁻¹ * (N * r ^ 2) *
        ((C * L * N * r ^ 2) ^ (-(3 / 2 : ℝ)) * L * (N * r)) ^ (-σ) := by
  rw [frostman_weight_identity (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hL) hN hr]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  · positivity
  · positivity

end WangZahlLot.Obl.wz_separated_scales_gain
