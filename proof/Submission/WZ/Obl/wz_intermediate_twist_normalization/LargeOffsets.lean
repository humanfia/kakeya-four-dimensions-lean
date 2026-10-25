-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.LargeOffsets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.CoarseEnergy
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Main
import Submission.WZ.Obl.wz_normalized_projection_iteration.Basic

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate
open WangZahlLot.Obl.wz_normalized_projection_iteration (Family)

/-- The lower bound resulting from the coarse energy estimate. -/
theorem coarse_area_lower {η δ r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hH : Family η δ n x v Y) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hF : CountF η δ n x v) {f : ℝ → ℝ} (hf : SlopeN f)
    (hc : 100 < |f 0|) (hrc : 1 ≤ r * (f 0) ^ 2)
    (K : ℕ) (hK : 5 ≤ 2 ^ K * r) :
    ENNReal.ofReal (δ ^ (3 * η + 1) * |f 0| / r) ≤
      ENNReal.ofReal (9000000 * (K + 1)) * volume (proj f (⋃ i, Y i)) := by
  obtain ⟨hn, hv, hT, _, hYm, hYT, hmass⟩ := hH
  have hC : 0 < |f 0| := by linarith
  have hL : 0 < (9000000 : ℝ) * (K + 1) := by positivity
  have hr : 0 < r := hδ.trans_le hδr
  let V := volume (proj f (⋃ i, Y i))
  by_cases hV : V = ⊤
  · change _ ≤ ENNReal.ofReal (9000000 * (K + 1)) * V
    rw [hV, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hL).ne']
    exact le_top
  have hVe : V = ENNReal.ofReal V.toReal := (ENNReal.ofReal_toReal hV).symm
  have henergy := coarse_energy hδ hδr hv hv2 hT hYm hYT hF hf hc hrc K hK
  have hsq : ENNReal.ofReal ((δ ^ η * (n : ℝ) * δ ^ 2) ^ 2) ≤
      V * ENNReal.ofReal
        (9000000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 3 * r / |f 0| * δ ^ (-η)) := by
    rw [ENNReal.ofReal_pow (by positivity)]
    exact (pow_le_pow_left₀ zero_le hmass 2).trans henergy
  rw [hVe, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hsq
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hsq
  have hcancel : δ ^ (-η) * δ ^ η = 1 := by rw [← Real.rpow_add hδ]; simp
  have hexp : δ ^ (3 * η + 1) = (δ ^ η) ^ 2 * δ ^ η * δ := by
    rw [show 3 * η + 1 = (η + η) + η + 1 by ring,
      Real.rpow_add hδ, Real.rpow_one, Real.rpow_add hδ, Real.rpow_add hδ]
    ring
  have hleft : (δ ^ η * (n : ℝ) * δ ^ 2) ^ 2 * (δ ^ η * |f 0|) =
      (δ ^ (3 * η + 1) * |f 0|) * ((n : ℝ) ^ 2 * δ ^ 3) := by rw [hexp]; ring
  have hright : (V.toReal *
      (9000000 * (K + 1) * (n : ℝ) ^ 2 * δ ^ 3 * r / |f 0| * δ ^ (-η))) *
      (δ ^ η * |f 0|) =
      (V.toReal * (9000000 * (K + 1)) * r) * ((n : ℝ) ^ 2 * δ ^ 3) := by
    calc _ = (V.toReal * (9000000 * (K + 1)) * r) * ((n : ℝ) ^ 2 * δ ^ 3) *
        (δ ^ (-η) * δ ^ η) := by field_simp
      _ = _ := by rw [hcancel, mul_one]
  have hscaled := mul_le_mul_of_nonneg_right hreal (show 0 ≤ δ ^ η * |f 0| by positivity)
  rw [hleft, hright] at hscaled
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hbase := le_of_mul_le_mul_right hscaled (show 0 < (n : ℝ) ^ 2 * δ ^ 3 by positivity)
  change _ ≤ ENNReal.ofReal (9000000 * (K + 1)) * V
  rw [hVe, ← ENNReal.ofReal_mul hL.le]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ hr]
  nlinarith

/-- In the intermediate regime the natural coarse radius is `|f 0|⁻²`. -/
theorem cubic_offset_lower {η δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hH : Family η δ n x v Y) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hF : CountF η δ n x v) {f : ℝ → ℝ} (hf : SlopeN f)
    (hc : 100 < |f 0|) (hδc : δ * (f 0) ^ 2 ≤ 1) :
    ∃ K : ℕ, 2 ^ K * δ ≤ 10 ∧
      ENNReal.ofReal (δ ^ (3 * η + 1) * |f 0| ^ 3) ≤
        ENNReal.ofReal (9000000 * (K + 1)) * volume (proj f (⋃ i, Y i)) := by
  have hC : 0 < |f 0| := by linarith
  have hc2 : 0 < |f 0| ^ 2 := by positivity
  let r := 1 / |f 0| ^ 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hδr : δ ≤ r := by
    rw [le_div_iff₀ hc2]
    simpa only [sq_abs] using hδc
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one hc2]
    nlinarith
  obtain ⟨K, hK5, hK10⟩ := exists_dyadic hr hr1
  refine ⟨K, (mul_le_mul_of_nonneg_left hδr (by positivity)).trans hK10, ?_⟩
  have hrc : 1 ≤ r * (f 0) ^ 2 := by
    dsimp [r]
    rw [sq_abs, one_div_mul_cancel (sq_pos_of_ne_zero (abs_pos.mp hC)).ne']
  have h := coarse_area_lower hδ hδr hH hv2 hF hf hc hrc K hK5
  convert h using 1
  congr 1
  dsimp [r]
  field_simp


lemma absorb_coarse_log {a δ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 < δ)
    (hd : δ ≤ (a / 180000000) ^ (1 / a)) {K : ℕ} (hK : 2 ^ K * δ ≤ 10) :
    (9000000 * (K + 1) : ℝ) * δ ^ (2 * a) ≤ 1 := by
  have hdyadic := nat_succ_le_rpow ha ha1 K
  have hpower : ((2 : ℝ) ^ K) ^ a * δ ^ a ≤ 10 := by
    rw [← Real.mul_rpow (by positivity) hδ.le]
    exact (Real.rpow_le_rpow (by positivity) hK ha.le).trans
      ((Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1).trans_eq (Real.rpow_one 10))
  have hlog : ((K : ℝ) + 1) * δ ^ a ≤ 20 / a := by
    calc ((K : ℝ) + 1) * δ ^ a ≤ (2 / a) * ((2 : ℝ) ^ K) ^ a * δ ^ a := by gcongr
      _ = (2 / a) * (((2 : ℝ) ^ K) ^ a * δ ^ a) := by ring
      _ ≤ (2 / a) * 10 := by gcongr
      _ = 20 / a := by ring
  have hsmall : δ ^ a ≤ a / 180000000 := by
    calc δ ^ a ≤ ((a / 180000000) ^ (1 / a)) ^ a :=
        Real.rpow_le_rpow hδ.le hd ha.le
      _ = a / 180000000 := by
        rw [← Real.rpow_mul (by positivity)]
        rw [one_div_mul_cancel ha.ne', Real.rpow_one]
  calc (9000000 * (K + 1) : ℝ) * δ ^ (2 * a) =
      9000000 * (((K : ℝ) + 1) * δ ^ a) * δ ^ a := by
        rw [two_mul, Real.rpow_add hδ]
        ring
    _ ≤ 9000000 * (20 / a) * (a / 180000000) := by gcongr
    _ = 1 := by field_simp; ring

/-- The full desired bound for the upper part of the intermediate offset range.
This estimate is independent of the bounded-offset hypothesis. -/
theorem uniform_large_intermediate : ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → (∀ i, (1 / 2 : ℝ) ≤ |v i 2|) →
      CountF η δ n x v → ∀ f : ℝ → ℝ, SlopeN f →
      100 < |f 0| → δ * (f 0) ^ 2 ≤ 1 →
      δ ^ (-(1 / 3 : ℝ) + min ε 1 / 4) ≤ |f 0| →
      ENNReal.ofReal (δ ^ ε) ≤ volume (proj f (⋃ i, Y i)) := by
  intro ε hε
  let e := min ε 1
  let a := e / 16
  have he : 0 < e := lt_min hε one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  refine ⟨e / 24, by positivity, (a / 180000000) ^ (1 / a), by positivity, ?_⟩
  intro δ hδ hd hδ100 n x v Y hH hv2 hF f hf hc hδc hoff
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨K, hK, harea⟩ := cubic_offset_lower hδ hH hv2 hF hf hc hδc
  have hlog := absorb_coarse_log ha ha1 hδ hd hK
  have hbudget : (9000000 * (K + 1) : ℝ) * δ ^ ε ≤ δ ^ (7 * e / 8) := by
    calc
      (9000000 * (K + 1) : ℝ) * δ ^ ε ≤ (9000000 * (K + 1) : ℝ) * δ ^ e := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 heε) (by positivity)
      _ = ((9000000 * (K + 1) : ℝ) * δ ^ (2 * a)) * δ ^ (7 * e / 8) := by
        rw [mul_assoc (9000000 * (K + 1) : ℝ), ← Real.rpow_add hδ]
        congr 2
        dsimp [a]
        ring
      _ ≤ δ ^ (7 * e / 8) := by
        calc _ ≤ 1 * δ ^ (7 * e / 8) := by gcongr
          _ = _ := one_mul _
  have hoffset : δ ^ (7 * e / 8) ≤ δ ^ (3 * (e / 24) + 1) * |f 0| ^ 3 := by
    calc
      δ ^ (7 * e / 8) = δ ^ (3 * (e / 24) + 1) * (δ ^ (-(1 / 3 : ℝ) + e / 4)) ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 1
        norm_num
        ring
      _ ≤ δ ^ (3 * (e / 24) + 1) * |f 0| ^ 3 := by gcongr
  have hL : 0 < (9000000 * (K + 1) : ℝ) := by positivity
  have hcomp : ENNReal.ofReal (9000000 * (K + 1)) * ENNReal.ofReal (δ ^ ε) ≤
      ENNReal.ofReal (9000000 * (K + 1)) * volume (proj f (⋃ i, Y i)) := by
    rw [← ENNReal.ofReal_mul hL.le]
    exact (ENNReal.ofReal_le_ofReal (hbudget.trans hoffset)).trans harea
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hL).ne'
    ENNReal.ofReal_ne_top).mp hcomp

end WangZahlLot.Obl.wz_intermediate_twist_normalization
