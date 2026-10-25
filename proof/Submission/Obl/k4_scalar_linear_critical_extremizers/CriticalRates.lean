/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/CriticalRates.lean.
-/

import Submission.Obl.k4_scalar_linear_critical_extremizers.Horizon

/-!
Critical density and time rates, with the near-minimal and near-maximal
choices made explicit. These are the order-theoretic constructions in
Section 4.1 of the supplied paper.
-/

namespace Submission.Obl.k4_scalar_linear_critical_extremizers

open Set Filter
open scoped Topology

noncomputable section

/-- Density caps supporting at least one positive-horizon problem. -/
def badDimensions {P : Type*} (admissible : P → Prop) (dimension horizon : P → ℝ) : Set ℝ :=
  {d | 0 ≤ d ∧ d < 1 ∧ ∃ p, admissible p ∧ dimension p ≤ d ∧ 0 < horizon p}

def criticalDimension {P : Type*} (admissible : P → Prop) (dimension horizon : P → ℝ) : ℝ :=
  sInf (badDimensions admissible dimension horizon)

theorem badDimensions_bddBelow {P : Type*}
    (admissible : P → Prop) (dimension horizon : P → ℝ) :
    BddBelow (badDimensions admissible dimension horizon) :=
  ⟨0, fun _ hd => hd.1⟩

theorem criticalDimension_nonneg {P : Type*}
    (admissible : P → Prop) (dimension horizon : P → ℝ)
    (hne : (badDimensions admissible dimension horizon).Nonempty) :
    0 ≤ criticalDimension admissible dimension horizon :=
  le_csInf hne (fun _ hd => hd.1)

theorem criticalDimension_le_bad {P : Type*}
    (admissible : P → Prop) (dimension horizon : P → ℝ)
    {p : P} (hp : admissible p) (hd₀ : 0 ≤ dimension p)
    (hd₁ : dimension p < 1) (hH : 0 < horizon p) :
    criticalDimension admissible dimension horizon ≤ dimension p :=
  csInf_le (badDimensions_bddBelow _ _ _) ⟨hd₀, hd₁, p, hp, le_rfl, hH⟩

theorem criticalDimension_lt_one {P : Type*}
    (admissible : P → Prop) (dimension horizon : P → ℝ)
    (hne : (badDimensions admissible dimension horizon).Nonempty) :
    criticalDimension admissible dimension horizon < 1 := by
  obtain ⟨d, hd⟩ := hne
  exact (csInf_le (badDimensions_bddBelow _ _ _) hd).trans_lt hd.2.1

/-- Every strictly larger cap supports a bad problem. The critical
density need not itself support one. -/
theorem exists_bad_below_cap {P : Type*}
    (admissible : P → Prop) (dimension horizon : P → ℝ)
    (hne : (badDimensions admissible dimension horizon).Nonempty)
    {d : ℝ} (hd : criticalDimension admissible dimension horizon < d) :
    ∃ p, admissible p ∧ dimension p < d ∧ 0 < horizon p := by
  obtain ⟨d', hd', hdd'⟩ := exists_lt_of_csInf_lt hne hd
  obtain ⟨p, hp, hpdim, hpH⟩ := hd'.2.2
  exact ⟨p, hp, hpdim.trans_lt hdd', hpH⟩

/-- A local slope strictly below the critical density has zero horizon
if arbitrarily small terminal extensions stay in that smaller cap. -/
theorem subcritical_horizon_eq_zero {P : Type*}
    (costs : P → Set ℝ) (dimension : P → ℝ) (dstar d tol : ℝ)
    (hcritical : ∀ q, 0 < sInf (costs q) → dstar ≤ dimension q)
    (hd : d < dstar) (htol : 0 < tol)
    (p : P) (hne : (costs p).Nonempty)
    (hcosts : ∀ h ∈ costs p, 0 ≤ h)
    (hext : ∀ h e, h ∈ costs p → 0 < e → e < h → e < tol →
      ∃ q, dimension q ≤ d ∧ sInf (costs p) ≤ h - e + sInf (costs q)) :
    sInf (costs p) = 0 := by
  have hnonneg := horizon_nonneg hne hcosts
  by_contra hzero
  have hbad : 0 < sInf (costs p) := lt_of_le_of_ne hnonneg (Ne.symm hzero)
  let e := min (sInf (costs p)) tol / 2
  have he : 0 < e := half_pos (lt_min hbad htol)
  have heH : e < sInf (costs p) := by
    have := min_le_left (sInf (costs p)) tol
    dsimp [e]
    linarith
  have hetol : e < tol := by
    have := min_le_right (sInf (costs p)) tol
    dsimp [e]
    linarith
  obtain ⟨h, hh, hhH⟩ := exists_lt_of_csInf_lt hne
    (lt_add_of_pos_right (sInf (costs p)) (show 0 < e / 4 by positivity))
  have hHh := csInf_le (show BddBelow (costs p) from ⟨0, hcosts⟩) hh
  obtain ⟨q, hqdim, hqH⟩ := hext h e hh he (heH.trans_le hHh) hetol
  have hqbad : 0 < sInf (costs q) := by linarith
  exact (not_le_of_gt hd) ((hcritical q hqbad).trans hqdim)

/-- Horizon-to-length ratios available below a density cap. -/
def horizonRates {P : Type*} (admissible : P → Prop)
    (dimension length horizon : P → ℝ) (d : ℝ) : Set ℝ :=
  {r | ∃ p, admissible p ∧ dimension p ≤ d ∧ r = horizon p / length p}

def extremalRate {P : Type*} (admissible : P → Prop)
    (dimension length horizon : P → ℝ) (d : ℝ) : ℝ :=
  sSup (horizonRates admissible dimension length horizon d)

theorem horizonRates_bddAbove {P : Type*} (admissible : P → Prop)
    (dimension length horizon : P → ℝ)
    (hbound : ∀ p, admissible p → 0 < length p ∧ horizon p ≤ length p) (d : ℝ) :
    BddAbove (horizonRates admissible dimension length horizon d) := by
  refine ⟨1, ?_⟩
  rintro r ⟨p, hp, hd, rfl⟩
  exact (div_le_one (hbound p hp).1).2 (hbound p hp).2

theorem horizon_le_extremalRate_mul {P : Type*} (admissible : P → Prop)
    (dimension length horizon : P → ℝ)
    (hbound : ∀ p, admissible p → 0 < length p ∧ horizon p ≤ length p)
    {p : P} (hp : admissible p) {d : ℝ} (hd : dimension p ≤ d) :
    horizon p ≤ extremalRate admissible dimension length horizon d * length p := by
  have hle := le_csSup (horizonRates_bddAbove _ _ _ _ hbound d)
    (show horizon p / length p ∈ horizonRates admissible dimension length horizon d from
      ⟨p, hp, hd, rfl⟩)
  exact (div_le_iff₀ (hbound p hp).1).1 hle

theorem extremalRate_mono {P : Type*} (admissible : P → Prop)
    (dimension length horizon : P → ℝ)
    (hbound : ∀ p, admissible p → 0 < length p ∧ horizon p ≤ length p)
    {d d' : ℝ} (hdd' : d ≤ d')
    (hne : (horizonRates admissible dimension length horizon d).Nonempty) :
    extremalRate admissible dimension length horizon d ≤
      extremalRate admissible dimension length horizon d' := by
  apply csSup_le_csSup (horizonRates_bddAbove _ _ _ _ hbound d') hne
  rintro r ⟨p, hp, hd, heq⟩
  exact ⟨p, hp, hd.trans hdd', heq⟩

theorem extremalRate_le_one {P : Type*} (admissible : P → Prop)
    (dimension length horizon : P → ℝ)
    (hbound : ∀ p, admissible p → 0 < length p ∧ horizon p ≤ length p)
    {d : ℝ} (hne : (horizonRates admissible dimension length horizon d).Nonempty) :
    extremalRate admissible dimension length horizon d ≤ 1 := by
  apply csSup_le hne
  rintro r ⟨p, hp, hd, rfl⟩
  exact (div_le_one (hbound p hp).1).2 (hbound p hp).2

/-- The right-hand limiting rate, defined without choosing a maximizing
problem at the critical density. -/
def criticalRate (rate : ℝ → ℝ) (dstar : ℝ) : ℝ :=
  sInf (rate '' Ioo dstar 1)

theorem criticalRate_le {rate : ℝ → ℝ} {dstar d : ℝ}
    (hbelow : ∀ d ∈ Ioo dstar 1, 0 ≤ rate d) (hd : d ∈ Ioo dstar 1) :
    criticalRate rate dstar ≤ rate d :=
  csInf_le ⟨0, by rintro _ ⟨d, hd, rfl⟩; exact hbelow d hd⟩ ⟨d, hd, rfl⟩

/-- Monotonicity identifies the right-hand rate limit along every
sequence of caps decreasing to the critical density from above. -/
theorem extremal_rates_tendsto_criticalRate {rate : ℝ → ℝ} {dstar : ℝ}
    (hstar : dstar < 1)
    (hbelow : ∀ d ∈ Ioo dstar 1, 0 ≤ rate d)
    (hmono : ∀ d ∈ Ioo dstar 1, ∀ d' ∈ Ioo dstar 1, d ≤ d' → rate d ≤ rate d')
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Ioo dstar 1) (hdlim : Tendsto d atTop (𝓝 dstar)) :
    Tendsto (fun i => rate (d i)) atTop (𝓝 (criticalRate rate dstar)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le (criticalRate_le hbelow (hd i))
  · intro b hb
    obtain ⟨t, ht⟩ := exists_between hstar
    have hne : (rate '' Ioo dstar 1).Nonempty := ⟨rate t, t, ht, rfl⟩
    obtain ⟨z, ⟨d', hd', rfl⟩, hz⟩ := exists_lt_of_csInf_lt hne hb
    have hdd' : ∀ᶠ i in atTop, d i < d' :=
      hdlim.eventually_lt tendsto_const_nhds hd'.1
    exact hdd'.mono fun i hi => (hmono _ (hd i) _ hd' hi.le).trans_lt hz

/-- A uniform lower rate on any right neighborhood remains positive at
the critical limit. -/
theorem criticalRate_pos {rate : ℝ → ℝ} {dstar α : ℝ}
    (hstar : dstar < 1) (hα : 0 < α)
    (hlower : ∀ d ∈ Ioo dstar 1, α ≤ rate d) :
    0 < criticalRate rate dstar := by
  obtain ⟨d, hd⟩ := exists_between hstar
  apply hα.trans_le
  apply le_csInf (show (rate '' Ioo dstar 1).Nonempty from ⟨rate d, d, hd, rfl⟩)
  rintro r ⟨d', hd', rfl⟩
  exact hlower d' hd'

end

end Submission.Obl.k4_scalar_linear_critical_extremizers
