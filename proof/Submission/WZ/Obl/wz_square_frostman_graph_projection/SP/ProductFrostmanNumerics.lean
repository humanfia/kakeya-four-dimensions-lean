-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ProductFrostmanNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.PowerBudget

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

theorem product_frostman_small_budget {δ η ν s : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hην : 4 * η ≤ ν) (hs : s ≤ 2) (hconst : 248832 ≤ δ ^ (-η)) :
    18 * 216 * (δ ^ (-η)) ^ 3 * (8 : ℝ) ^ s ≤ δ ^ (-ν) := by
  have h8 : (8 : ℝ) ^ s ≤ 64 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hs
    norm_num at hh
    exact hh
  calc
    18 * 216 * (δ ^ (-η)) ^ 3 * (8 : ℝ) ^ s ≤ 248832 * (δ ^ (-η)) ^ 3 := by nlinarith [pow_nonneg (Real.rpow_nonneg hδ.le (-η)) 3]
    _ ≤ δ ^ (-η) * (δ ^ (-η)) ^ 3 := mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = δ ^ (-4 * η) := by rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]; congr 1; norm_num; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

theorem product_frostman_large_budget {δ η ν p r s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hp : 0 < p) (hpν : p ≤ ν / 10) (hην : η ≤ ν / 100)
    (hs : 0 ≤ s) (hs2 : s ≤ 2) (hr : δ ^ p / 8 ≤ r)
    (hconst : 248832 ≤ δ ^ (-η)) : 1 ≤ δ ^ (-ν) * r ^ s := by
  have ht : 0 < δ ^ p / 8 := by positivity
  have ht1 : δ ^ p / 8 ≤ 1 := by have hh := Real.rpow_le_one hδ.le hδ1 hp.le; linarith
  have hpow : (δ ^ p / 8) ^ (2 : ℕ) ≤ r ^ s := by
    calc
      (δ ^ p / 8) ^ (2 : ℕ) = (δ ^ p / 8) ^ (2 : ℝ) := by norm_num
      _ ≤ (δ ^ p / 8) ^ s := Real.rpow_le_rpow_of_exponent_ge ht ht1 hs2
      _ ≤ _ := Real.rpow_le_rpow ht.le hr hs
  have h64 : (64 : ℝ) ≤ δ ^ (2 * p - ν) :=
    ((by norm_num : (64 : ℝ) ≤ 248832).trans hconst).trans
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  calc
    (1 : ℝ) ≤ δ ^ (2 * p - ν) / 64 := by linarith
    _ = δ ^ (-ν) * (δ ^ p / 8) ^ (2 : ℕ) := by
      rw [div_pow, ← Real.rpow_mul_natCast hδ.le]
      have hid : δ ^ (-ν) * (δ ^ (p * (2 : ℕ)) / 8 ^ (2 : ℕ)) =
          (δ ^ (-ν) * δ ^ (p * (2 : ℕ))) / 64 := by norm_num; ring
      rw [hid, ← Real.rpow_add hδ]
      congr 1; norm_num; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hδ.le _)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
