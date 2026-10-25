-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.LowRingNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RingNumerics
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.TruncatedEnergy

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

theorem low_ring_ratio_scale {δ : ℝ} (hδ : 0 < δ) :
    16 * δ / (δ ^ (1 / 1000 : ℝ) * δ ^ (1 / 1000 : ℝ)) = 16 * δ ^ (499 / 500 : ℝ) := by
  rw [← Real.rpow_add hδ]
  calc
    16 * δ / δ ^ (1 / 1000 + 1 / 1000 : ℝ) = 16 * (δ ^ (1 : ℝ) / δ ^ (1 / 500 : ℝ)) := by norm_num; ring
    _ = _ := by rw [← Real.rpow_sub hδ]; norm_num

theorem low_ring_power_bounds {δ C σ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 < κ) (hσ : 100000 * κ ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (hC : 0 ≤ C) (hCb : C ≤ δ ^ (-κ))
    (hconst : max 128 (5120 * energyConstant (3 / 4)) ≤ δ ^ (-κ)) :
    320 * C ^ 2 * energyConstant (3 / 4) *
        (16 * δ / (δ ^ (1 / 1000 : ℝ) * δ ^ (1 / 1000 : ℝ))) ^ (3 * σ / 2) ≤ δ ^ (σ + 10 * κ) ∧
      C ^ 3 * (128 * δ * δ ^ (1 / 1000 : ℝ)) ^ σ ≤ δ ^ (σ + 10 * κ) := by
  have hσ0 : 0 ≤ σ := by linarith
  have hE : 0 < energyConstant (3 / 4) := energyConstant_pos (by norm_num)
  have h128 : (128 : ℝ) ≤ δ ^ (-κ) := (le_max_left _ _).trans hconst
  have h5120 : 5120 * energyConstant (3 / 4) ≤ δ ^ (-κ) := (le_max_right _ _).trans hconst
  constructor
  · rw [low_ring_ratio_scale hδ, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hδ.le _),
      ← Real.rpow_mul hδ.le]
    have h16 : (16 : ℝ) ^ (3 * σ / 2) ≤ 16 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16)
        (show 3 * σ / 2 ≤ 1 by linarith)
    calc
      320 * C ^ 2 * energyConstant (3 / 4) *
          ((16 : ℝ) ^ (3 * σ / 2) * δ ^ ((499 / 500) * (3 * σ / 2))) ≤
          (5120 * energyConstant (3 / 4)) * C ^ 2 * δ ^ ((499 / 500) * (3 * σ / 2)) := by
        have hh := mul_le_mul_of_nonneg_left h16 (show 0 ≤ 320 * C ^ 2 * energyConstant (3 / 4) *
            δ ^ ((499 / 500) * (3 * σ / 2)) by positivity)
        convert hh using 1 <;> ring
      _ ≤ δ ^ (-κ) * (δ ^ (-κ)) ^ 2 * δ ^ ((499 / 500) * (3 * σ / 2)) := by gcongr
      _ = δ ^ ((499 / 500) * (3 * σ / 2) - 3 * κ) := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1; norm_num; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  · have h128σ : (128 : ℝ) ^ σ ≤ 128 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 128)
        (show σ ≤ 1 by linarith)
    have heq : (128 * δ * δ ^ (1 / 1000 : ℝ)) ^ σ =
        (128 : ℝ) ^ σ * δ ^ ((1001 / 1000) * σ) := by
      have hid : 128 * δ * δ ^ (1 / 1000 : ℝ) = 128 * δ ^ (1001 / 1000 : ℝ) := by
        calc
          128 * δ * δ ^ (1 / 1000 : ℝ) = 128 * (δ ^ (1 : ℝ) * δ ^ (1 / 1000 : ℝ)) := by rw [Real.rpow_one]; ring
          _ = _ := by rw [← Real.rpow_add hδ]; norm_num
      rw [hid, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
    rw [heq]
    calc
      C ^ 3 * ((128 : ℝ) ^ σ * δ ^ ((1001 / 1000) * σ)) ≤
          (δ ^ (-κ)) ^ 3 * (δ ^ (-κ) * δ ^ ((1001 / 1000) * σ)) := by
        gcongr
        exact h128σ.trans h128
      _ = δ ^ ((1001 / 1000) * σ - 4 * κ) := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1; norm_num; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
