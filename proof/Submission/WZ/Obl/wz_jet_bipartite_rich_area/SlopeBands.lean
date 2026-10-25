-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.SlopeBands.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.Obl.wz_jet_close_pair_moment.Measure
import Submission.WZ.Obl.wz_multiscale_finite_tower.LogLoss

/-!
# Dyadic slope-band summation for narrow strip-intersection unions

A narrow union (pairs whose slope gap is below `cap`, inside a time window) is covered
by the natural band `[0, s₀]` and the dyadic bands `[s₀ 2^k, s₀ 2^(k+1)]`, `k < K`,
as soon as `cap ≤ s₀ 2^K`. If each band has area at most `V`, the narrow union has
area at most `(K + 1) V`; `K = log₂ ⌈cap/s₀⌉ + 1` works and is at most
`1 + log₂ (cap/s₀ + 1)`.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open WangZahlLot.Obl.wz_jet_close_pair_moment (strip)

/-- Points of the strip-intersection union over `F × G`, in the time window `[l, u]`,
whose witnessing pair has slope gap in `[lo, hi]`. -/
def slopeBandUnion {n : ℕ} (F G : Finset (Fin n)) (g : Fin n → ℝ → ℝ)
    (δ l u lo hi : ℝ) : Set (ℝ × ℝ) :=
  ⋃ i ∈ F, ⋃ j ∈ G, {p | p ∈ strip δ (g i) ∧ p ∈ strip δ (g j) ∧ p.2 ∈ Icc l u ∧
    lo ≤ |deriv (g i) p.2 - deriv (g j) p.2| ∧ |deriv (g i) p.2 - deriv (g j) p.2| ≤ hi}

/-- The narrow strip-intersection union in the time window `[l, u]`: slope gap below
`cap`. -/
def narrowWindowUnion {n : ℕ} (F G : Finset (Fin n)) (g : Fin n → ℝ → ℝ)
    (δ l u cap : ℝ) : Set (ℝ × ℝ) :=
  ⋃ i ∈ F, ⋃ j ∈ G, {p | p ∈ strip δ (g i) ∧ p ∈ strip δ (g j) ∧ p.2 ∈ Icc l u ∧
    |deriv (g i) p.2 - deriv (g j) p.2| < cap}

/-- A gap above `s₀` and below `s₀ 2^K` lies in one dyadic band `[s₀ 2^k, s₀ 2^(k+1)]`
with `k < K`. -/
private theorem exists_dyadic_band {s₀ x : ℝ} {K : ℕ} (hx₀ : s₀ < x)
    (hxK : x ≤ s₀ * 2 ^ K) : ∃ k < K, s₀ * 2 ^ k ≤ x ∧ x ≤ s₀ * 2 ^ (k + 1) := by
  have hex : ∃ k, x ≤ s₀ * 2 ^ (k + 1) := by
    rcases K with _ | K
    · simp at hxK; linarith
    · exact ⟨K, hxK⟩
  classical
  let k := Nat.find hex
  have hk : x ≤ s₀ * 2 ^ (k + 1) := Nat.find_spec hex
  have hkK : k < K := by
    rcases K with _ | K
    · simp at hxK; linarith
    · exact Nat.lt_succ_of_le (Nat.find_min' hex hxK)
  refine ⟨k, hkK, ?_, hk⟩
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero, mul_one]; exact hx₀.le
  · have hmin := Nat.find_min hex (show k - 1 < k by omega)
    rw [not_le, Nat.sub_add_cancel hpos] at hmin
    exact hmin.le

/-- The narrow union is covered by the natural band and the dyadic bands. -/
theorem narrowWindowUnion_subset_bands {n : ℕ} (F G : Finset (Fin n))
    (g : Fin n → ℝ → ℝ) (δ l u : ℝ) {s₀ cap : ℝ} {K : ℕ} (hK : cap ≤ s₀ * 2 ^ K) :
    narrowWindowUnion F G g δ l u cap ⊆
      slopeBandUnion F G g δ l u 0 s₀ ∪
        ⋃ k ∈ Finset.range K, slopeBandUnion F G g δ l u (s₀ * 2 ^ k) (s₀ * 2 ^ (k + 1)) := by
  intro p hp
  simp only [narrowWindowUnion, mem_iUnion, mem_ofPred_eq] at hp
  obtain ⟨i, hi, j, hj, hpi, hpj, hpt, hgap⟩ := hp
  set x := |deriv (g i) p.2 - deriv (g j) p.2|
  by_cases hsmall : x ≤ s₀
  · left
    simp only [slopeBandUnion, mem_iUnion, mem_ofPred_eq]
    exact ⟨i, hi, j, hj, hpi, hpj, hpt, abs_nonneg _, hsmall⟩
  · right
    obtain ⟨k, hk, hlo, hhi⟩ := exists_dyadic_band (lt_of_not_ge hsmall) (hgap.le.trans hK)
    simp only [slopeBandUnion, mem_iUnion, mem_ofPred_eq, Finset.mem_range]
    exact ⟨k, hk, i, hi, j, hj, hpi, hpj, hpt, hlo, hhi⟩

/-- **Dyadic slope summation.** If the natural band and each of the `K` dyadic bands
have area at most `V`, and `cap ≤ s₀ 2^K`, the narrow union has area at most
`(K + 1) V`. -/
theorem volume_narrowWindowUnion_le_of_bands {n : ℕ} (F G : Finset (Fin n))
    (g : Fin n → ℝ → ℝ) (δ l u : ℝ) {s₀ cap V : ℝ} {K : ℕ} (hV : 0 ≤ V)
    (hK : cap ≤ s₀ * 2 ^ K)
    (hnat : volume (slopeBandUnion F G g δ l u 0 s₀) ≤ ENNReal.ofReal V)
    (hdy : ∀ k < K,
      volume (slopeBandUnion F G g δ l u (s₀ * 2 ^ k) (s₀ * 2 ^ (k + 1))) ≤
        ENNReal.ofReal V) :
    volume (narrowWindowUnion F G g δ l u cap) ≤ ENNReal.ofReal ((K + 1) * V) := by
  calc
    _ ≤ volume (slopeBandUnion F G g δ l u 0 s₀ ∪
        ⋃ k ∈ Finset.range K, slopeBandUnion F G g δ l u (s₀ * 2 ^ k) (s₀ * 2 ^ (k + 1))) :=
      measure_mono (narrowWindowUnion_subset_bands F G g δ l u hK)
    _ ≤ volume (slopeBandUnion F G g δ l u 0 s₀) +
        volume (⋃ k ∈ Finset.range K,
          slopeBandUnion F G g δ l u (s₀ * 2 ^ k) (s₀ * 2 ^ (k + 1))) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal V + ∑ k ∈ Finset.range K,
          volume (slopeBandUnion F G g δ l u (s₀ * 2 ^ k) (s₀ * 2 ^ (k + 1))) :=
      add_le_add hnat (measure_biUnion_finset_le _ _)
    _ ≤ ENNReal.ofReal V + ∑ _k ∈ Finset.range K, ENNReal.ofReal V := by
      gcongr with k hk
      exact hdy k (Finset.mem_range.mp hk)
    _ = ENNReal.ofReal ((K + 1) * V) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add hV (by positivity)]
      congr 1
      ring

/-- An explicit number of dyadic bands: `K = log₂ ⌈cap/s₀⌉ + 1` reaches the cap. -/
theorem le_mul_two_pow_bandCount {s₀ cap : ℝ} (hs₀ : 0 < s₀) :
    cap ≤ s₀ * 2 ^ (Nat.log 2 ⌈cap / s₀⌉₊ + 1) := by
  have hceil : cap / s₀ ≤ (⌈cap / s₀⌉₊ : ℝ) := Nat.le_ceil _
  have hpow : (⌈cap / s₀⌉₊ : ℝ) < (2 : ℝ) ^ (Nat.log 2 ⌈cap / s₀⌉₊ + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) _
  have h := hceil.trans hpow.le
  rw [div_le_iff₀ hs₀] at h
  linarith

/-- The band count is logarithmic: `log₂ ⌈cap/s₀⌉ + 1 ≤ 1 + log₂ (cap/s₀ + 1)`. -/
theorem bandCount_le_logb {s₀ cap : ℝ} (hs₀ : 0 < s₀) (hcap : 0 ≤ cap) :
    ((Nat.log 2 ⌈cap / s₀⌉₊ + 1 : ℕ) : ℝ) ≤ 1 + Real.logb 2 (cap / s₀ + 1) := by
  set m := ⌈cap / s₀⌉₊
  have hq : 0 ≤ cap / s₀ := div_nonneg hcap hs₀.le
  have hm : (m : ℝ) ≤ cap / s₀ + 1 := (Nat.ceil_lt_add_one hq).le
  push_cast
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0, Nat.log_zero_right, Nat.cast_zero]
    have : 0 ≤ Real.logb 2 (cap / s₀ + 1) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    linarith
  · have hlog : ((Nat.log 2 m : ℕ) : ℝ) ≤ Real.logb 2 m := by
      have h2m : ((2 : ℕ) : ℝ) ^ (Nat.log 2 m) ≤ (m : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hpos)]
      rw [Real.rpow_natCast]
      exact_mod_cast h2m
    have hmono : Real.logb 2 m ≤ Real.logb 2 (cap / s₀ + 1) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) hm
    linarith

/-- **Dyadic slope summation, logarithmic form.** With `K = log₂ ⌈cap/s₀⌉ + 1` bands,
the narrow union has area at most `(2 + log₂ (cap/s₀ + 1)) V`. -/
theorem volume_narrowWindowUnion_le_log {n : ℕ} (F G : Finset (Fin n))
    (g : Fin n → ℝ → ℝ) (δ l u : ℝ) {s₀ cap V : ℝ} (hs₀ : 0 < s₀) (hcap : 0 ≤ cap)
    (hV : 0 ≤ V)
    (hnat : volume (slopeBandUnion F G g δ l u 0 s₀) ≤ ENNReal.ofReal V)
    (hdy : ∀ k < Nat.log 2 ⌈cap / s₀⌉₊ + 1,
      volume (slopeBandUnion F G g δ l u (s₀ * 2 ^ k) (s₀ * 2 ^ (k + 1))) ≤
        ENNReal.ofReal V) :
    volume (narrowWindowUnion F G g δ l u cap) ≤
      ENNReal.ofReal ((2 + Real.logb 2 (cap / s₀ + 1)) * V) := by
  refine (volume_narrowWindowUnion_le_of_bands F G g δ l u hV
    (le_mul_two_pow_bandCount hs₀) hnat hdy).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := bandCount_le_logb hs₀ hcap
  push_cast at h ⊢
  nlinarith

/-- The dyadic bands stop below `2 cap + 2 s₀`: every band top `s₀ 2^(k+1)`, `k < K`,
satisfies this (so below `4 cap` once `s₀ ≤ cap`). -/
theorem bandTop_le {s₀ cap : ℝ} (hs₀ : 0 < s₀) (hcap : 0 ≤ cap) {k : ℕ}
    (hk : k < Nat.log 2 ⌈cap / s₀⌉₊ + 1) :
    s₀ * 2 ^ (k + 1) ≤ 2 * cap + 2 * s₀ := by
  set m := ⌈cap / s₀⌉₊
  have hq : 0 ≤ cap / s₀ := div_nonneg hcap hs₀.le
  have hm : (m : ℝ) ≤ cap / s₀ + 1 := (Nat.ceil_lt_add_one hq).le
  have hpow : s₀ * 2 ^ (k + 1) ≤ s₀ * 2 ^ (Nat.log 2 m + 1) := by
    gcongr
    · norm_num
    · omega
  refine hpow.trans ?_
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0, Nat.log_zero_right]; norm_num; linarith
  · have h2m : (2 : ℝ) ^ (Nat.log 2 m) ≤ m := by
      exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
    have hcm : s₀ * (m : ℝ) ≤ cap + s₀ := by
      have := mul_le_mul_of_nonneg_left hm hs₀.le
      rw [mul_add, mul_div_cancel₀ _ hs₀.ne', mul_one] at this
      exact this
    calc
      s₀ * 2 ^ (Nat.log 2 m + 1) = 2 * (s₀ * 2 ^ (Nat.log 2 m)) := by ring
      _ ≤ 2 * (s₀ * m) := by gcongr
      _ ≤ 2 * (cap + s₀) := by gcongr
      _ = _ := by ring

theorem bandTop_le_four_mul {s₀ cap : ℝ} (hs₀ : 0 < s₀) (hs₀cap : s₀ ≤ cap) {k : ℕ}
    (hk : k < Nat.log 2 ⌈cap / s₀⌉₊ + 1) :
    s₀ * 2 ^ (k + 1) ≤ 4 * cap := by
  have := bandTop_le hs₀ (hs₀.le.trans hs₀cap) hk
  linarith

/-- The band factor at the natural scale `s₀ = sqrt(δ D)` is logarithmic in `δ`. -/
theorem bandFactor_le_log {δ D cap : ℝ} (hδ : 0 < δ) (hδD : δ ≤ D) (hD20 : D ≤ 20)
    (hcap0 : 0 ≤ cap) (hcapD : cap ≤ D) :
    2 + Real.logb 2 (cap / Real.sqrt (δ * D) + 1) ≤ 6 * (1 + |Real.log δ|) := by
  have hD : 0 < D := hδ.trans_le hδD
  set s₀ := Real.sqrt (δ * D)
  have hs₀ : 0 < s₀ := Real.sqrt_pos.mpr (mul_pos hδ hD)
  have hs₀sq : s₀ ^ 2 = δ * D := Real.sq_sqrt (mul_pos hδ hD).le
  set x := cap / s₀ + 1
  have hx1 : 1 ≤ x := by
    have : 0 ≤ cap / s₀ := div_nonneg hcap0 hs₀.le
    linarith
  -- (cap/s₀ + 1)^2 ≤ 4 D / δ
  have hq2 : (cap / s₀) ^ 2 ≤ D / δ := by
    rw [div_pow, hs₀sq, div_le_div_iff₀ (mul_pos hδ hD) hδ]
    nlinarith [mul_le_mul hcapD hcapD hcap0 hD.le]
  have hone : (1 : ℝ) ≤ D / δ := (one_le_div hδ).mpr hδD
  have hx2 : x ^ 2 ≤ 4 * (D / δ) := by
    have hq0 : 0 ≤ cap / s₀ := div_nonneg hcap0 hs₀.le
    nlinarith [sq_nonneg (cap / s₀ - 1)]
  have hlogx : 2 * Real.log x ≤ Real.log 4 + Real.log D - Real.log δ := by
    have hxpos : 0 < x := by linarith
    have h := Real.log_le_log (by positivity) hx2
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity),
      Real.log_div hD.ne' hδ.ne'] at h
    push_cast at h
    linarith
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlogD : Real.log D ≤ 5 * Real.log 2 := by
    have h := Real.log_le_log hD (hD20.trans (by norm_num : (20 : ℝ) ≤ 2 ^ 5))
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlogδ : -Real.log δ ≤ |Real.log δ| := neg_le_abs _
  have hlb : Real.logb 2 x = Real.log x / Real.log 2 := rfl
  have hl2pos : 0 < Real.log 2 := by linarith
  have hbound : Real.logb 2 x ≤ 3.5 + |Real.log δ| := by
    rw [hlb, div_le_iff₀ hl2pos]
    have habs : 0 ≤ |Real.log δ| := abs_nonneg _
    nlinarith
  have habs : 0 ≤ |Real.log δ| := abs_nonneg _
  linarith

/-- **Band-count absorption.** For `0 < δ ≤ 1`, `δ ≤ D ≤ 20`, `0 ≤ cap ≤ D` and any
`ε > 0`, the band factor at `s₀ = sqrt(δ D)` is at most `6 (1 + 1/ε) δ^(-ε)`. -/
theorem bandFactor_le_rpow {δ D cap ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδD : δ ≤ D)
    (hD20 : D ≤ 20) (hcap0 : 0 ≤ cap) (hcapD : cap ≤ D) (hε : 0 < ε) :
    2 + Real.logb 2 (cap / Real.sqrt (δ * D) + 1) ≤ 6 * (1 + 1 / ε) * δ ^ (-ε) := by
  have h1 := bandFactor_le_log hδ hδD hD20 hcap0 hcapD
  have h2 := WangZahlLot.Obl.wz_multiscale_finite_tower.one_add_abs_log_le_rpow hδ hδ1 hε
  calc
    _ ≤ 6 * (1 + |Real.log δ|) := h1
    _ ≤ 6 * ((1 + 1 / ε) * δ ^ (-ε)) := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
