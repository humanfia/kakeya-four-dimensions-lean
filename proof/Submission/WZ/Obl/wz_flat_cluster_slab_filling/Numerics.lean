-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.Numerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Basic

/-!
The asymptotic choice of `d₀` for the proof of `WangZahlLot.wz_flat_cluster_slab_filling`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Classical

/-- For `p > 0` and `C > 0`, `δ ^ p ≤ C` for all small enough `δ > 0`. -/
lemma num_eventually_rpow_le {p C : ℝ} (hp : 0 < p) (hC : 0 < C) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ^ p ≤ C := by
  refine ⟨C ^ p⁻¹, Real.rpow_pos_of_pos hC _, fun δ hδ hδd => ?_⟩
  calc δ ^ p ≤ (C ^ p⁻¹) ^ p := Real.rpow_le_rpow hδ.le hδd hp.le
    _ = C := Real.rpow_inv_rpow hC.le hp.ne'

/-- If `0 < δ ≤ 1`, `δ ^ q ≤ C` and `x + q ≤ y`, then `δ ^ y ≤ δ ^ x * C`. -/
lemma num_rpow_split {δ x y q C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : x + q ≤ y)
    (hC : δ ^ q ≤ C) : δ ^ y ≤ δ ^ x * C :=
  calc δ ^ y ≤ δ ^ (x + q) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hq
    _ = δ ^ x * δ ^ q := Real.rpow_add hδ x q
    _ ≤ δ ^ x * C := mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg hδ.le x)

/-- The logarithmic smallness condition (the last one of `numerics`), for a general
constant `K > 0`: it follows from `δ ^ (e / 4) ≤ 1 / (K * (1 + 4 / e) * 6144 ^ (1 / β))`
as soon as `3 * a + a' / β ≤ e / 2`. -/
lemma num_log_condition {β e K δ a a' : ℝ} (he : 0 < e) (hK : 0 < K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hexp : 3 * a + a' * (1 / β) ≤ e / 2)
    (hsmall : δ ^ (e / 4) ≤ 1 / (K * (1 + 4 / e) * (6144 : ℝ) ^ (1 / β))) :
    δ ^ e * (K * (1 + Real.log (1 / δ))) ≤ δ ^ (3 * a) * (δ ^ a' / 6144) ^ (1 / β) := by
  have hs : (0 : ℝ) < (6144 : ℝ) ^ (1 / β) := Real.rpow_pos_of_pos (by norm_num) _
  set s : ℝ := (6144 : ℝ) ^ (1 / β) with hs_def
  set u : ℝ := δ ^ (e / 4) with hu_def
  have hu : 0 < u := Real.rpow_pos_of_pos hδ _
  have hu1 : u ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have hv : δ ^ (e / 2) = u * u := by
    rw [hu_def, ← Real.rpow_add hδ]; congr 1; ring
  have hw : δ ^ e = u * u * u * u := by
    rw [hu_def, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
  -- lower bound for the right-hand side
  have hR : u * u / s ≤ δ ^ (3 * a) * (δ ^ a' / 6144) ^ (1 / β) := by
    have h1 : (δ ^ a' / 6144) ^ (1 / β) = δ ^ (a' * (1 / β)) / s := by
      rw [Real.div_rpow (Real.rpow_nonneg hδ.le _) (by norm_num), ← Real.rpow_mul hδ.le]
    have h2 : δ ^ (3 * a) * (δ ^ (a' * (1 / β)) / s) = δ ^ (3 * a + a' * (1 / β)) / s := by
      rw [Real.rpow_add hδ]; ring
    rw [h1, h2, ← hv]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp) hs.le
  -- the logarithm: `log (1 / δ) ≤ (1 / δ) ^ (e / 4) / (e / 4)`
  have hL0 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hL : u * Real.log (1 / δ) ≤ 4 / e := by
    have h1 := Real.log_le_rpow_div (x := 1 / δ) (ε := e / 4) (by positivity) (by positivity)
    rw [Real.div_rpow zero_le_one hδ.le, Real.one_rpow, ← hu_def] at h1
    calc u * Real.log (1 / δ) ≤ u * (1 / u / (e / 4)) := mul_le_mul_of_nonneg_left h1 hu.le
      _ = 4 / e := by field_simp
  -- the smallness of `u`
  have hpos : 0 < K * (1 + 4 / e) * s := by positivity
  have hsm : K * (1 + 4 / e) * u ≤ 1 / s := by
    have h1 : u * (K * (1 + 4 / e) * s) ≤ 1 := (le_div_iff₀ hpos).1 hsmall
    rw [le_div_iff₀ hs]
    calc K * (1 + 4 / e) * u * s = u * (K * (1 + 4 / e) * s) := by ring
      _ ≤ 1 := h1
  calc δ ^ e * (K * (1 + Real.log (1 / δ)))
      = K * (u * u * u) * (u + u * Real.log (1 / δ)) := by rw [hw]; ring
    _ ≤ K * (u * u * u) * (1 + 4 / e) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = u * u * (K * (1 + 4 / e) * u) := by ring
    _ ≤ u * u * (1 / s) := mul_le_mul_of_nonneg_left hsm (by positivity)
    _ = u * u / s := by ring
    _ ≤ _ := hR

/-- All the smallness conditions on `δ` used in the proof, uniformly in the exponents
`a = h + η ≤ 2ε` and `a' = h + 2η ≤ 3ε`, where `ε = min e c * min β 1 / 20`. -/
lemma numerics {β c e : ℝ} (hβ : 0 < β) (hc : 0 < c) (he : 0 < e) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ a a' : ℝ, 0 < a → a ≤ 2 * (min e c * min β 1 / 20) →
        0 < a' → a' ≤ 3 * (min e c * min β 1 / 20) →
        δ ^ e ≤ δ ^ a / 6144 ∧
        δ ^ (c * β) ≤ δ ^ a' / 6144 ∧
        (32 * δ ^ c) ^ β ≤ δ ^ a' / 6144 ∧
        δ ^ c ≤ 1 / 16 ∧
        δ ^ (min c 1 / 2) ≤ 1 / 96 ∧
        δ ^ e * ((10 ^ 13 * 768 ^ 2 * 16 * 16000 ^ 2 : ℝ) * (1 + Real.log (1 / δ))) ≤
          δ ^ (3 * a) * (δ ^ a' / 6144) ^ (1 / β) := by
  -- `k = min e c`, `m = min β 1`, `ε = k * m / 20`
  have hm0 : 0 < min β 1 := lt_min hβ one_pos
  have hm1 : min β 1 ≤ 1 := min_le_right _ _
  have hmβ : min β 1 ≤ β := min_le_left _ _
  have hke : min e c ≤ e := min_le_left _ _
  have hkc : min e c ≤ c := min_le_right _ _
  have hkm_e : min e c * min β 1 ≤ e := by
    calc min e c * min β 1 ≤ e * 1 := mul_le_mul hke hm1 hm0.le he.le
      _ = e := mul_one e
  have hkm_cβ : min e c * min β 1 ≤ c * β := mul_le_mul hkc hmβ hm0.le hc.le
  have hkm_eβ : min e c * min β 1 ≤ e * β := mul_le_mul hke hmβ hm0.le he.le
  have hK : (0 : ℝ) < 10 ^ 13 * 768 ^ 2 * 16 * 16000 ^ 2 := by norm_num
  have h32 : (0 : ℝ) < (32 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  have hs : (0 : ℝ) < (6144 : ℝ) ^ (1 / β) := Real.rpow_pos_of_pos (by norm_num) _
  have hmc : 0 < min c 1 := lt_min hc one_pos
  -- one threshold for each smallness condition
  obtain ⟨d1, hd1, H1⟩ := num_eventually_rpow_le (p := 9 * e / 10) (C := 1 / 6144)
    (by positivity) (by norm_num)
  obtain ⟨d2, hd2, H2⟩ := num_eventually_rpow_le (p := 17 * (c * β) / 20) (C := 1 / 6144)
    (by positivity) (by norm_num)
  obtain ⟨d3, hd3, H3⟩ := num_eventually_rpow_le (p := 17 * (c * β) / 20)
    (C := 1 / (6144 * (32 : ℝ) ^ β)) (by positivity) (by positivity)
  obtain ⟨d4, hd4, H4⟩ := num_eventually_rpow_le (p := c) (C := 1 / 16) hc (by norm_num)
  obtain ⟨d5, hd5, H5⟩ := num_eventually_rpow_le (p := min c 1 / 2) (C := 1 / 96)
    (by positivity) (by norm_num)
  obtain ⟨d6, hd6, H6⟩ := num_eventually_rpow_le (p := e / 4)
    (C := 1 / ((10 ^ 13 * 768 ^ 2 * 16 * 16000 ^ 2 : ℝ) * (1 + 4 / e) * (6144 : ℝ) ^ (1 / β)))
    (by positivity) (by positivity)
  refine ⟨min (1 / 100) (min d1 (min d2 (min d3 (min d4 (min d5 d6))))), ?_,
    min_le_left _ _, ?_⟩
  · simp only [lt_min_iff]
    exact ⟨by norm_num, hd1, hd2, hd3, hd4, hd5, hd6⟩
  intro δ hδ hδd a a' ha hae ha' ha'e
  simp only [le_min_iff] at hδd
  obtain ⟨h100, hδd1, hδd2, hδd3, hδd4, hδd5, hδd6⟩ := hδd
  have hδ1 : δ ≤ 1 := by linarith
  -- the exponent bookkeeping
  have hq1 : a + 9 * e / 10 ≤ e := by linarith
  have hq2 : a' + 17 * (c * β) / 20 ≤ c * β := by linarith
  have hexp : 3 * a + a' * (1 / β) ≤ e / 2 := by
    have h1 : a' * (1 / β) ≤ 3 * e / 20 := by
      rw [mul_one_div, div_le_iff₀ hβ]; linarith
    linarith
  refine ⟨?_, ?_, ?_, H4 δ hδ hδd4, H5 δ hδ hδd5, ?_⟩
  · -- `δ ^ e ≤ δ ^ a / 6144`
    calc δ ^ e ≤ δ ^ a * (1 / 6144) := num_rpow_split hδ hδ1 hq1 (H1 δ hδ hδd1)
      _ = δ ^ a / 6144 := by ring
  · -- `δ ^ (c * β) ≤ δ ^ a' / 6144`
    calc δ ^ (c * β) ≤ δ ^ a' * (1 / 6144) := num_rpow_split hδ hδ1 hq2 (H2 δ hδ hδd2)
      _ = δ ^ a' / 6144 := by ring
  · -- `(32 * δ ^ c) ^ β ≤ δ ^ a' / 6144`
    have hpow : (32 * δ ^ c) ^ β = (32 : ℝ) ^ β * δ ^ (c * β) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le]
    have hb : δ ^ (c * β) ≤ δ ^ a' * (1 / (6144 * (32 : ℝ) ^ β)) :=
      num_rpow_split hδ hδ1 hq2 (H3 δ hδ hδd3)
    rw [hpow]
    have h32' : (32 : ℝ) ^ β ≠ 0 := h32.ne'
    calc (32 : ℝ) ^ β * δ ^ (c * β)
        ≤ (32 : ℝ) ^ β * (δ ^ a' * (1 / (6144 * (32 : ℝ) ^ β))) :=
          mul_le_mul_of_nonneg_left hb h32.le
      _ = δ ^ a' / 6144 := by field_simp
  · -- the logarithmic condition
    exact num_log_condition he hK hδ hδ1 hexp (H6 δ hδ hδd6)

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
