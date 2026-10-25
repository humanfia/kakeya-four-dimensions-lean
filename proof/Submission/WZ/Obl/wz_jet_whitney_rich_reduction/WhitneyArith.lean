-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_whitney_rich_reduction.WhitneyArith.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Arithmetic for the Whitney reduction (x0284)

* `numScales δ = ⌈log_{3/2} (20/δ)⌉₊ + 2` scales suffice: `20 < δ (3/2)^(L-1)`;
* `numScales_le`: `L ≤ (3 * 20^t / t + 3) δ^(-t)` for every `t > 0`, `0 < δ ≤ 1`;
* `le_rpow_neg_of_le`: `δ ≤ C^(-1/s)` gives `C ≤ δ^(-s)`.
-/

namespace WangZahlLot.Obl.wz_jet_whitney_rich_reduction

noncomputable section

/-- Number of Whitney scales used at resolution `δ`. -/
def numScales (δ : ℝ) : ℕ := ⌈Real.logb (3 / 2) (20 / δ)⌉₊ + 2

lemma one_le_numScales (δ : ℝ) : 1 ≤ numScales δ := by
  unfold numScales; omega

lemma numScales_spec {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    20 < δ * (3 / 2 : ℝ) ^ (numScales δ - 1) := by
  unfold numScales
  set x := Real.logb (3 / 2) (20 / δ) with hx
  have h20 : (0 : ℝ) < 20 / δ := by positivity
  have hpow : (3 / 2 : ℝ) ^ x = 20 / δ := Real.rpow_logb (by norm_num) (by norm_num) h20
  have hk : (⌈x⌉₊ + 2 - 1 : ℕ) = ⌈x⌉₊ + 1 := by omega
  rw [hk]
  have h1 : (3 / 2 : ℝ) ^ x ≤ (3 / 2 : ℝ) ^ (⌈x⌉₊ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil x)
  rw [Real.rpow_natCast] at h1
  have h2 : (3 / 2 : ℝ) ^ (⌈x⌉₊ + 1) = (3 / 2) ^ ⌈x⌉₊ * (3 / 2) := pow_succ _ _
  rw [h2]
  rw [hpow] at h1
  have h3 : 20 ≤ δ * (3 / 2 : ℝ) ^ ⌈x⌉₊ := by
    rw [div_le_iff₀' hδ] at h1
    linarith
  have h4 : 0 < (3 / 2 : ℝ) ^ ⌈x⌉₊ := by positivity
  nlinarith

lemma log_three_halves_ge : (1 / 3 : ℝ) ≤ Real.log (3 / 2) := by
  have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  norm_num at this ⊢
  linarith

lemma numScales_le {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 < t) :
    (numScales δ : ℝ) ≤ (3 * 20 ^ t / t + 3) * δ ^ (-t) := by
  unfold numScales
  set x := Real.logb (3 / 2) (20 / δ) with hx
  have h20 : (1 : ℝ) ≤ 20 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hlog0 : 0 ≤ Real.log (20 / δ) := Real.log_nonneg h20
  have hx0 : 0 ≤ x := by
    rw [hx, Real.logb]
    exact div_nonneg hlog0 (Real.log_nonneg (by norm_num))
  have hceil : ((⌈x⌉₊ : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hxle : x ≤ 3 * Real.log (20 / δ) := by
    rw [hx, Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have := log_three_halves_ge
    nlinarith
  have hlogle : Real.log (20 / δ) ≤ (20 / δ) ^ t / t :=
    Real.log_le_rpow_div (by positivity) ht
  have hpow : (20 / δ) ^ t = 20 ^ t * δ ^ (-t) := by
    rw [Real.div_rpow (by norm_num) hδ.le, Real.rpow_neg hδ.le, div_eq_mul_inv]
  have hδt : 1 ≤ δ ^ (-t) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have h20t : 0 < (20 : ℝ) ^ t := by positivity
  push_cast
  calc (⌈x⌉₊ : ℝ) + 2 ≤ x + 3 := by linarith
    _ ≤ 3 * ((20 / δ) ^ t / t) + 3 := by linarith
    _ = 3 * 20 ^ t / t * δ ^ (-t) + 3 := by rw [hpow]; ring
    _ ≤ 3 * 20 ^ t / t * δ ^ (-t) + 3 * δ ^ (-t) := by linarith
    _ = (3 * 20 ^ t / t + 3) * δ ^ (-t) := by ring

/-- `δ ≤ C^(-1/s)` gives `C ≤ δ^(-s)`. -/
lemma le_rpow_neg_of_le {C s δ : ℝ} (hC : 0 < C) (hs : 0 < s) (hδ : 0 < δ)
    (h : δ ≤ C ^ (-1 / s)) : C ≤ δ ^ (-s) := by
  have h1 : (C ^ (-1 / s)) ^ (-s) ≤ δ ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hδ h (by linarith)
  have h2 : (C ^ (-1 / s)) ^ (-s) = C := by
    rw [← Real.rpow_mul hC.le]
    have : -1 / s * -s = 1 := by field_simp
    rw [this, Real.rpow_one]
  linarith

end

end WangZahlLot.Obl.wz_jet_whitney_rich_reduction
