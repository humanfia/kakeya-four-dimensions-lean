-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.UniformArithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

lemma count_sqrt_cancel {D δ N : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hN : 0 < N) (q : ℝ) :
    (D * δ ^ (-q) * N * δ ^ 2) ^ (-(1 / 2 : ℝ)) * Real.sqrt N =
      D ^ (-(1 / 2 : ℝ)) * δ ^ (q / 2 - 1) := by
  have hbase : D * δ ^ (-q) * N * δ ^ 2 = (D * N) * δ ^ (2 - q) := by
    rw [show (2 - q : ℝ) = -q + 2 by ring, Real.rpow_add hδ, Real.rpow_two]
    ring
  have hNpow : N ^ (-(1 / 2 : ℝ)) * Real.sqrt N = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN]
    norm_num
  rw [hbase, Real.mul_rpow (mul_nonneg hD.le hN.le) (Real.rpow_nonneg hδ.le _),
    Real.mul_rpow hD.le hN.le, ← Real.rpow_mul hδ.le]
  rw [show (2 - q) * (-(1 / 2 : ℝ)) = q / 2 - 1 by ring]
  calc
    _ = D ^ (-(1 / 2 : ℝ)) * δ ^ (q / 2 - 1) *
      (N ^ (-(1 / 2 : ℝ)) * Real.sqrt N) := by ring
    _ = _ := by rw [hNpow, mul_one]

lemma sharp_fine_power {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) (C q c : ℝ) :
    (c * δ ^ ((3 / 2 : ℝ) + q) * (δ ^ (C * q) * δ ^ q) ^ 3 *
      (56 * δ ^ (-q) * N * δ ^ 2) ^ (-(1 / 2 : ℝ))) *
      (δ ^ (C * q) * δ ^ q) / ((8 * C) * δ ^ (-q)) * Real.sqrt N =
    (c / (8 * C) * (56 : ℝ) ^ (-(1 / 2 : ℝ))) *
      δ ^ ((1 / 2 : ℝ) + (4 * C + 13 / 2) * q) := by
  have hL : (δ ^ (C * q) * δ ^ q) ^ 3 * (δ ^ (C * q) * δ ^ q) =
      δ ^ (4 * (C + 1) * q) := by
    rw [← pow_succ, ← Real.rpow_add hδ, ← Real.rpow_natCast (δ ^ (C * q + q)) 4,
      ← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hinv : (δ ^ (-q))⁻¹ = δ ^ q := by rw [Real.rpow_neg hδ.le, inv_inv]
  calc
    _ = (c / (8 * C)) *
        ((56 * δ ^ (-q) * N * δ ^ 2) ^ (-(1 / 2 : ℝ)) * Real.sqrt N) *
        ((δ ^ (C * q) * δ ^ q) ^ 3 * (δ ^ (C * q) * δ ^ q)) *
        δ ^ ((3 / 2 : ℝ) + q) * (δ ^ (-q))⁻¹ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (c / (8 * C) * (56 : ℝ) ^ (-(1 / 2 : ℝ))) *
        (δ ^ (q / 2 - 1) * δ ^ (4 * (C + 1) * q) *
          δ ^ ((3 / 2 : ℝ) + q) * δ ^ q) := by
      rw [count_sqrt_cancel (by norm_num) hδ hN, hL, hinv]
      ring
    _ = _ := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 2
      ring

lemma sharp_coarse_power {δ : ℝ} (hδ : 0 < δ) (C q : ℝ) :
    (δ ^ (C * q) * δ ^ q) ^ 2 * δ ^ q = δ ^ ((2 * C + 3) * q) := by
  rw [← Real.rpow_add hδ, ← Real.rpow_two (δ ^ (C * q + q)),
    ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
  congr 1
  ring

lemma coarse_cancel {δ N G s V L q : ℝ} (hδ : 0 < δ) (hN : 0 < N)
    (hG : 0 < G)
    (h : L ^ 2 * N * δ ^ 2 * s ^ 2 ≤ (56 * δ ^ (-q) * N * δ ^ 2 * G) * V) :
    (s ^ 2 / (56 * G)) * (L ^ 2 * δ ^ q) ≤ V := by
  have hcancel : L ^ 2 * s ^ 2 ≤ (56 * δ ^ (-q) * G) * V := by
    apply (mul_le_mul_iff_left₀ (mul_pos hN (sq_pos_of_pos hδ))).mp
    convert h using 1 <;> ring
  have hp : 0 < 56 * δ ^ (-q) * G := by positivity
  have hd : L ^ 2 * s ^ 2 / (56 * δ ^ (-q) * G) ≤ V :=
    (div_le_iff₀ hp).mpr (by nlinarith only [hcancel])
  convert hd using 1
  simp only [div_eq_mul_inv, mul_inv_rev, Real.rpow_neg hδ.le, inv_inv]
  ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
