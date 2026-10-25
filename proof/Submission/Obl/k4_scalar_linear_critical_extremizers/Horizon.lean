/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/Horizon.lean.
-/

import Mathlib

/-!
Infimum and composition arguments for the minimum horizon. The geometric
inputs are left explicit: these lemmas do not assume an infimum is attained.
See the supplied paper, `def:horizon`, `a03:composition`, and
`a03:positive-rate`.
-/

namespace Submission.Obl.k4_scalar_linear_critical_extremizers

open Set

/-- Horizon costs are nonnegative, so their nonempty infimum is too. -/
theorem horizon_nonneg {costs : Set ℝ} (hne : costs.Nonempty)
    (hcosts : ∀ h ∈ costs, 0 ≤ h) : 0 ≤ sInf costs :=
  le_csInf hne hcosts

/-- Lifting each nearly optimal terminal system through an outer atlas
adds its fixed horizon cost to the infimum. -/
theorem horizon_composition {outer inner : Set ℝ} {h : ℝ}
    (houter : BddBelow outer) (hinner : inner.Nonempty)
    (hlift : ∀ b ∈ inner, h + b ∈ outer) :
    sInf outer ≤ h + sInf inner := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hb, hbε⟩ := exists_lt_of_csInf_lt hinner
    (lt_add_of_pos_right (sInf inner) hε)
  have hout := csInf_le houter (hlift b hb)
  linarith

/-- Two infima can be composed without requiring either one to be
realized by a terminal system. -/
theorem horizon_composition_infima {outer first second : Set ℝ}
    (houter : BddBelow outer) (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hlift : ∀ a ∈ first, ∀ b ∈ second, a + b ∈ outer) :
    sInf outer ≤ sInf first + sInf second := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, ha, haε⟩ := exists_lt_of_csInf_lt hfirst
    (lt_add_of_pos_right (sInf first) (half_pos hε))
  obtain ⟨b, hb, hbε⟩ := exists_lt_of_csInf_lt hsecond
    (lt_add_of_pos_right (sInf second) (half_pos hε))
  have hout := csInf_le houter (hlift a ha b hb)
  linarith

/-- The zero-horizon conclusion supplies every requested positive horizon
and accuracy budget. The two budgets may be chosen independently. -/
theorem small_systems_of_zero_horizon
    {Good : ℝ → ℝ → Prop}
    (hmono : ∀ h h' ε ε' : ℝ, h ≤ h' → ε ≤ ε' → Good h ε → Good h' ε')
    (hne : {a : ℝ | 0 ≤ a ∧ ∀ ε : ℝ, 0 < ε → Good (a + ε) ε}.Nonempty)
    (hzero : sInf {a : ℝ | 0 ≤ a ∧ ∀ ε : ℝ, 0 < ε → Good (a + ε) ε} = 0) :
    ∀ h ε : ℝ, 0 < h → 0 < ε → Good h ε := by
  intro h ε hh hε
  obtain ⟨a, ha, hah⟩ := exists_lt_of_csInf_lt hne (by simpa [hzero] using hh)
  let δ := min ε ((h - a) / 2)
  have hδ : 0 < δ := lt_min hε (half_pos (sub_pos.mpr hah))
  have hδe : δ ≤ ε := min_le_left _ _
  have hδh : a + δ ≤ h := by
    have := min_le_right ε ((h - a) / 2)
    dsimp [δ]
    linarith
  exact hmono (a + δ) h δ ε hδh hδe (ha.2 δ hδ)

/-- Conversely, systems at every positive pair of budgets force the
minimum horizon to vanish. -/
theorem zero_horizon_of_small_systems {Good : ℝ → ℝ → Prop}
    (hsmall : ∀ h ε : ℝ, 0 < h → 0 < ε → Good h ε) :
    sInf {a : ℝ | 0 ≤ a ∧ ∀ ε : ℝ, 0 < ε → Good (a + ε) ε} = 0 := by
  let costs := {a : ℝ | 0 ≤ a ∧ ∀ ε : ℝ, 0 < ε → Good (a + ε) ε}
  have h₀ : (0 : ℝ) ∈ costs := by
    refine ⟨le_rfl, ?_⟩
    intro ε hε
    simpa using hsmall ε ε hε hε
  exact le_antisymm (csInf_le ⟨0, fun _ hx => hx.1⟩ h₀)
    (horizon_nonneg ⟨0, h₀⟩ fun _ hx => hx.1)

/-- A uniform terminal-extension constant gives a uniform positive lower
bound for the extremal time rate. The remaining problem may depend on
both the chosen near-minimal system and its extension tolerance. -/
theorem positive_rate_of_terminal_extension {P : Type*}
    (costs : P → Set ℝ) (length : P → ℝ) (C c k : ℝ)
    (hC : 0 < C) (hc : 0 < c)
    (hcosts : ∀ p h, h ∈ costs p → 0 ≤ h)
    (hrate : ∀ p, 0 < length p ∧ sInf (costs p) ≤ k * length p)
    (hext : ∀ p h e, h ∈ costs p → 0 < e → e < h → e < c * length p →
      ∃ q, length q ≤ C * e ∧ sInf (costs p) ≤ h - e + sInf (costs q))
    (p : P) (hne : (costs p).Nonempty) (hbad : 0 < sInf (costs p)) :
    3 / (4 * C) ≤ k := by
  have hcL : 0 < c * length p := mul_pos hc (hrate p).1
  let e := min (sInf (costs p)) (c * length p) / 2
  have he : 0 < e := half_pos (lt_min hbad hcL)
  have heH : e < sInf (costs p) := by
    have := min_le_left (sInf (costs p)) (c * length p)
    dsimp [e]
    linarith
  have heL : e < c * length p := by
    have := min_le_right (sInf (costs p)) (c * length p)
    dsimp [e]
    linarith
  obtain ⟨h, hh, hhH⟩ := exists_lt_of_csInf_lt hne
    (lt_add_of_pos_right (sInf (costs p)) (show 0 < e / 4 by positivity))
  have hHh := csInf_le (show BddBelow (costs p) from ⟨0, hcosts p⟩) hh
  obtain ⟨q, hqL, hqH⟩ := hext p h e hh he (heH.trans_le hHh) heL
  have hq := (hrate q).2
  have hk : 0 < k := by
    have hq₀ : 0 < sInf (costs q) := by linarith
    have hprod : 0 < k * length q := hq₀.trans_le hq
    exact (mul_pos_iff_of_pos_right (hrate q).1).mp hprod
  have hmul : k * length q ≤ k * (C * e) :=
    mul_le_mul_of_nonneg_left hqL hk.le
  apply (div_le_iff₀ (show 0 < 4 * C by positivity)).2
  nlinarith

end Submission.Obl.k4_scalar_linear_critical_extremizers
