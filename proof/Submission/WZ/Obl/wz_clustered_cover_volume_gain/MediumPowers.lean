-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.MediumPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainScales

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

lemma packet_count_power_bound {δ ε : ℝ} {A : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hA : (A : ℝ) ≤ 2 * δ ^ (-ε)) :
    (((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) ≤ (513 : ℝ) ^ 6 * δ ^ (-(12 * ε)) := by
  have hpow : 1 ≤ δ ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hA2 := pow_le_pow_left₀ (Nat.cast_nonneg A) hA 2
  have hone := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hpow 2
  have hraw : 128 * (A : ℝ) ^ 2 + 1 ≤ 513 * (δ ^ (-ε)) ^ 2 := by nlinarith
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 128 * (A : ℝ) ^ 2 + 1) hraw 6
  push_cast
  calc
    _ ≤ (513 * (δ ^ (-ε)) ^ 2) ^ 6 := hh
    _ = 513 ^ 6 * δ ^ (-(12 * ε)) := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_mul_natCast hδ.le]
      congr 2
      push_cast
      ring

/-- Normalize all medium-scale losses into one fine-scale exponent. -/
theorem medium_volume_factor_bound {δ r w m D C K Cg σ ω e ν χ β : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hC : 0 < C) (hK : 0 < K) (hCg : 0 < Cg)
    (hm : 0 ≤ m) (hσ : 0 ≤ σ) (hω : 0 ≤ ω)
    (hD : δ ^ ν ≤ D) (hmUpper : m ≤ K * δ ^ (-χ))
    (hw : (δ ^ β / Cg) * r ^ 2 ≤ w) :
    C * δ ^ (-e) * (D / 8)⁻¹ * m ^ (1 + σ / 2) * w ^ (-(ω + σ) / 2) ≤
      (C * 8 * K ^ (1 + σ / 2) * Cg ^ ((ω + σ) / 2)) *
        δ ^ (-(e + ν + χ * (1 + σ / 2) + β * (ω + σ) / 2)) * r ^ (-ω - σ) := by
  have hDpos : 0 < D := (Real.rpow_pos_of_pos hδ ν).trans_le hD
  have hwpos : 0 < w := (by positivity : 0 < (δ ^ β / Cg) * r ^ 2).trans_le hw
  have hDi : (D / 8)⁻¹ ≤ (δ ^ ν / 8)⁻¹ :=
    inv_anti₀ (by positivity) (div_le_div_of_nonneg_right hD (by norm_num))
  have hmp : m ^ (1 + σ / 2) ≤ (K * δ ^ (-χ)) ^ (1 + σ / 2) :=
    Real.rpow_le_rpow hm hmUpper (by linarith)
  have hwp : w ^ (-(ω + σ) / 2) ≤ ((δ ^ β / Cg) * r ^ 2) ^ (-(ω + σ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hw (by linarith)
  calc
    _ ≤ C * δ ^ (-e) * (δ ^ ν / 8)⁻¹ * (K * δ ^ (-χ)) ^ (1 + σ / 2) *
        ((δ ^ β / Cg) * r ^ 2) ^ (-(ω + σ) / 2) := by
      gcongr
    _ = _ := by
      apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
        (by simp only [Set.mem_Ioi]; positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_inv, Real.log_div, Real.log_rpow, Real.log_pow]
      ring

lemma medium_loss_bound {e ν b h σ ω : ℝ}
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : ω ≤ 1) :
    2 * e + ν + (12 * b + h) * (1 + σ / 2) + b * (ω + σ) / 2 ≤
      2 * e + ν + 16 * b + 2 * h := by
  have hp := mul_le_mul_of_nonneg_left hσhalf (show 0 ≤ 12 * b + h by positivity)
  have hq := mul_le_mul_of_nonneg_left (show ω + σ ≤ 3 / 2 by linarith) hb
  nlinarith

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
