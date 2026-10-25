/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/Maximizing.lean.
-/

import Submission.Obl.k4_scalar_linear_critical_extremizers.CriticalRates

/-!
Near-maximizers in the critical density class. Every chosen term is an
actual admissible problem. No problem at the density or horizon infimum
is assumed to realize either optimum.
-/

namespace Submission.Obl.k4_scalar_linear_critical_extremizers

open Set Filter
open scoped Topology

noncomputable section

/-- Normalization to length one and approximate suprema produce an
actual maximizing sequence. Its own density caps, and its own extremal
rates, converge to the critical values. -/
theorem exists_maximizing_sequence_along_caps {P : Type*}
    (admissible : P → Prop) (dimension length horizon : P → ℝ)
    (hbound : ∀ p, admissible p → 0 < length p ∧ horizon p ≤ length p)
    (hdim : ∀ p, admissible p → 0 ≤ dimension p ∧ dimension p < 1)
    (hne : (badDimensions admissible dimension horizon).Nonempty)
    (hnormalize : ∀ p, admissible p → ∃ q, admissible q ∧ length q = 1 ∧
      dimension q = dimension p ∧ horizon q = horizon p / length p)
    (caps err : ℕ → ℝ)
    (hcaps : ∀ i, caps i ∈ Ioo (criticalDimension admissible dimension horizon) 1)
    (hcapslim : Tendsto caps atTop (𝓝 (criticalDimension admissible dimension horizon)))
    (herr : ∀ i, 0 < err i) (herrlim : Tendsto err atTop (𝓝 0)) :
    ∃ p : ℕ → P,
      (∀ i, admissible (p i) ∧ length (p i) = 1 ∧ 0 < horizon (p i)) ∧
      Tendsto (fun i => dimension (p i)) atTop
        (𝓝 (criticalDimension admissible dimension horizon)) ∧
      Tendsto (fun i => horizon (p i)) atTop
        (𝓝 (criticalRate (extremalRate admissible dimension length horizon)
          (criticalDimension admissible dimension horizon))) ∧
      Tendsto (fun i => extremalRate admissible dimension length horizon (dimension (p i)))
        atTop (𝓝 (criticalRate (extremalRate admissible dimension length horizon)
          (criticalDimension admissible dimension horizon))) := by
  let dstar := criticalDimension admissible dimension horizon
  let rate := extremalRate admissible dimension length horizon
  let k := criticalRate rate dstar
  have hstar : dstar < 1 := criticalDimension_lt_one _ _ _ hne
  have hnonempty (d : ℝ) (hd : d ∈ Ioo dstar 1) :
      (horizonRates admissible dimension length horizon d).Nonempty := by
    obtain ⟨p, hp, hpdim, hpH⟩ := exists_bad_below_cap _ _ _ hne hd.1
    exact ⟨horizon p / length p, p, hp, hpdim.le, rfl⟩
  have hratepos (d : ℝ) (hd : d ∈ Ioo dstar 1) : 0 < rate d := by
    obtain ⟨p, hp, hpdim, hpH⟩ := exists_bad_below_cap _ _ _ hne hd.1
    exact (div_pos hpH (hbound p hp).1).trans_le
      (le_csSup (horizonRates_bddAbove _ _ _ _ hbound d) ⟨p, hp, hpdim.le, rfl⟩)
  have hrate₀ (d : ℝ) (hd : d ∈ Ioo dstar 1) : 0 ≤ rate d := (hratepos d hd).le
  have hratelim : Tendsto (fun i => rate (caps i)) atTop (𝓝 k) :=
    extremal_rates_tendsto_criticalRate hstar hrate₀
      (fun d hd d' hd' hdd' => extremalRate_mono _ _ _ _ hbound hdd' (hnonempty d hd))
      caps hcaps hcapslim
  have hexists (i : ℕ) : ∃ q, admissible q ∧ length q = 1 ∧ 0 < horizon q ∧
      dimension q ≤ caps i ∧ rate (caps i) - err i ≤ horizon q ∧
      horizon q ≤ rate (caps i) := by
    have hmax : max 0 (rate (caps i) - err i) < rate (caps i) :=
      max_lt (hratepos _ (hcaps i)) (sub_lt_self _ (herr i))
    obtain ⟨r, ⟨p, hp, hpdim, rfl⟩, hnear⟩ :=
      exists_lt_of_lt_csSup (hnonempty _ (hcaps i)) hmax
    obtain ⟨q, hq, hqlen, hqdim, hqH⟩ := hnormalize p hp
    have hqpos : 0 < horizon q := by
      rw [hqH]
      exact (le_max_left _ _).trans_lt hnear
    have hqnear : rate (caps i) - err i ≤ horizon q := by
      rw [hqH]
      exact ((le_max_right _ _).trans_lt hnear).le
    have hqupper : horizon q ≤ rate (caps i) := by
      have := horizon_le_extremalRate_mul _ _ _ _ hbound hq (hqdim ▸ hpdim)
      simpa only [hqlen, mul_one] using this
    exact ⟨q, hq, hqlen, hqpos, hqdim ▸ hpdim, hqnear, hqupper⟩
  choose p hp hlen hpos hcap hlower hupper using hexists
  have hdimlower (i : ℕ) : dstar ≤ dimension (p i) :=
    criticalDimension_le_bad _ _ _ (hp i) (hdim _ (hp i)).1 (hdim _ (hp i)).2 (hpos i)
  have hdimlim : Tendsto (fun i => dimension (p i)) atTop (𝓝 dstar) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcapslim hdimlower hcap
  have hHlim : Tendsto (fun i => horizon (p i)) atTop (𝓝 k) := by
    have hlo := hratelim.sub herrlim
    simp only [sub_zero] at hlo
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hratelim hlower hupper
  have hownlower (i : ℕ) : horizon (p i) ≤ rate (dimension (p i)) := by
    have := horizon_le_extremalRate_mul _ _ _ _ hbound (hp i) (le_rfl (a := dimension (p i)))
    simpa only [hlen i, mul_one] using this
  have hownupper (i : ℕ) : rate (dimension (p i)) ≤ rate (caps i) :=
    extremalRate_mono _ _ _ _ hbound (hcap i)
      ⟨horizon (p i) / length (p i), p i, hp i, le_rfl, rfl⟩
  refine ⟨p, fun i => ⟨hp i, hlen i, hpos i⟩, hdimlim, hHlim, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hHlim hratelim hownlower hownupper

end

end Submission.Obl.k4_scalar_linear_critical_extremizers
