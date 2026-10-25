/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/ConcreteCritical.lean.
-/

import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces
import Submission.Obl.k4_scalar_linear_critical_extremizers.CriticalRates
import Submission.Obl.k4_scalar_linear_critical_extremizers.CriticalProfiles
import Submission.Obl.k4_scalar_linear_critical_extremizers.Maximizing

set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_linear_critical_extremizers.Split

open Set Filter
open scoped Topology

noncomputable section

theorem weakCalculus_of_calculus (hcalc : Calculus) : WeakCalculus := by
  refine ⟨hcalc.1, hcalc.2.1, ?_⟩
  intro p r b h d' hp hr₀ hrL hrb hbL hd₀ hd₁ hcap hKnown
  obtain ⟨q, hq, hqL, hqd, hqS, hqU, href, hH, hprof, heq⟩ :=
    hcalc.2.2 p r b h d' hp hr₀ hrL hrb hbL hd₀ hd₁ hcap hKnown
  exact ⟨q, hq, hqL, hqd, hqS, hqU, hH, hprof, heq⟩

/-- Changing a density-cap parameter leaves all measures and chart costs
unchanged. It is the same exact sequence with a different terminal cap. -/
def setCap (p : Code) (δ : ℝ) : Code :=
  ⟨W p, N p, K p, M p, D p, L p, δ, S p, U p, ω p, ν p, E p, g p, G p, f p⟩

theorem setCap_length (p : Code) (δ : ℝ) : L (setCap p δ) = L p := rfl
theorem setCap_dimension (p : Code) (δ : ℝ) : d (setCap p δ) = δ := rfl
theorem setCap_angular (p : Code) (δ : ℝ) : S (setCap p δ) = S p := rfl
theorem setCap_angularLength (p : Code) (δ : ℝ) : U (setCap p δ) = U p := rfl
theorem setCap_profile (p : Code) (δ : ℝ) : f (setCap p δ) = f p := rfl
theorem setCap_cost (p : Code) (δ h : ℝ) : Cost (setCap p δ) h ↔ Cost p h := Iff.rfl
theorem setCap_horizon (p : Code) (δ : ℝ) : Horizon (setCap p δ) = Horizon p := rfl

theorem setCap_exact (p : Code) (hp : Exact p) (δ : ℝ)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (hcap : ∀ r : ℝ, 0 ≤ r → r ≤ L p → f p (L p) - f p r ≤ δ * (L p - r)) :
    Exact (setCap p δ) := by
  obtain ⟨⟨hN, hNt, hK, hM, hD, hL, hd₀, hd₁, hS, hU⟩,
    h1, h2, h3, h4, h5, h6, h7⟩ := hp
  exact ⟨⟨hN, hNt, hK, hM, hD, hL, hδ₀, hδ₁, hS, hU⟩,
    h1, h2, h3, h4, h5, hcap, h7⟩

theorem exact_length_pos {p : Code} (hp : Exact p) : 0 < L p := by
  obtain ⟨⟨_, _, _, _, _, hL, _⟩, _⟩ := hp
  exact hL

theorem exact_dimension_bounds {p : Code} (hp : Exact p) : 0 ≤ d p ∧ d p < 1 := by
  obtain ⟨⟨_, _, _, _, _, _, hd₀, hd₁, _⟩, _⟩ := hp
  exact ⟨hd₀, hd₁⟩

theorem exact_angular_pos {p : Code} (hp : Exact p) : 0 < S p ∧ 0 < U p := by
  obtain ⟨⟨_, _, _, _, _, _, _, _, hS, hU⟩, _⟩ := hp
  exact ⟨hS, hU⟩

theorem exact_profile_regular {p : Code} (hp : Exact p) :
    ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L p →
      0 ≤ f p s - f p r ∧ f p s - f p r ≤ s - r := hp.2.2.2.2.1

theorem exact_terminal_cap {p : Code} (hp : Exact p) :
    ∀ r : ℝ, 0 ≤ r → r ≤ L p → f p (L p) - f p r ≤ d p * (L p - r) :=
  hp.2.2.2.2.2.2.1

theorem horizon_nonneg_of_initial (hinit : Initial) {p : Code} (hp : Exact p) :
    0 ≤ Horizon p :=
  le_csInf ⟨L p, hinit p hp⟩ (fun _ hh => hh.1)

theorem horizon_le_length_of_initial (hinit : Initial) {p : Code} (hp : Exact p) :
    Horizon p ≤ L p := csInf_le ⟨0, fun _ hh => hh.1⟩ (hinit p hp)

/-- The angular parameters held fixed during the critical optimization. -/
def AngularClass (S₀ η : ℝ) (p : Code) : Prop :=
  Exact p ∧ S p = S₀ ∧ U p = η * L p

/-- A locally subcritical terminal cap has zero horizon. Apply terminal
extension so little that its entire remaining interval lies in the local
cap, then normalize that actual atlas to contradict the critical density. -/
theorem local_subcritical_horizon_zero (hinit : Initial) (hcalc : WeakCalculus) (hext : Extension)
    (S₀ η dstar δ : ℝ) (hS : 0 < S₀) (hη : 0 < η)
    (hcrit : ∀ q, AngularClass S₀ η q → 0 < Horizon q → dstar ≤ d q)
    (hδ₀ : 0 ≤ δ) (hδstar : δ < dstar) (hδ₁ : δ < 1)
    (p : Code) (hp : AngularClass S₀ η p) (a : ℝ) (_ha₀ : 0 ≤ a) (ha : a < L p)
    (hcap : ∀ t ∈ Icc a (L p), f p (L p) - f p t ≤ δ * (L p - t)) :
    Horizon p = 0 := by
  obtain ⟨C, c, hC, hc, hExtension⟩ :=
    hext (d p) S₀ η (exact_dimension_bounds hp.1).1
      (exact_dimension_bounds hp.1).2 hS hη
  let tol := min (c * L p) ((L p - a) / C)
  have htol : 0 < tol := lt_min (mul_pos hc (exact_length_pos hp.1))
    (div_pos (sub_pos.mpr ha) hC)
  refine subcritical_horizon_eq_zero
    (P := {q : Code // AngularClass S₀ η q})
    (costs := fun q => {h : ℝ | Cost q.1 h}) (dimension := fun q => d q.1)
    (dstar := dstar) (d := δ) (tol := tol) (fun q hq => hcrit q.1 q.2 hq) hδstar htol
    ⟨p, hp⟩ ⟨L p, hinit p hp.1⟩ (fun _ hh => hh.1) ?_
  intro h e hh he heh hetol
  have hec : e < c * L p := hetol.trans_le (min_le_left _ _)
  obtain ⟨r, hr₀, hrL, hrem, hKnown⟩ :=
    hExtension p hp.1 le_rfl hp.2.1 hp.2.2 h e (he.trans heh) hh he heh hec
  have herem : C * e < L p - a := by
    have hdiv : e < (L p - a) / C := hetol.trans_le (min_le_right _ _)
    have := (lt_div_iff₀ hC).1 hdiv
    nlinarith
  have har : a < r := by linarith
  obtain ⟨q, hq, hqL, hqd, hqS, hqU, hH, hprofile, heq⟩ :=
    hcalc.2.2 p r (L p) (h - e) δ hp.1 hr₀.le hrL hrL.le le_rfl hδ₀ hδ₁
      (fun t hrt htL => hcap t ⟨har.le.trans hrt, htL⟩) hKnown
  have hqclass : AngularClass S₀ η q := by
    refine ⟨hq, hqS.trans hp.2.1, ?_⟩
    rw [hqU, hp.2.2, hqL]
    field_simp [(exact_length_pos hp.1).ne']
  exact ⟨⟨q, hqclass⟩, hqd.le, hH⟩

theorem angularClass_unit_normalization (hcalc : WeakCalculus) (S₀ η : ℝ)
    (p : Code) (hp : AngularClass S₀ η p) :
    ∃ q, AngularClass S₀ η q ∧ L q = 1 ∧ d q = d p ∧ Horizon q = Horizon p / L p := by
  obtain ⟨q, hq, hqL, hqd, hqS, hqU, hqH, hprof⟩ :=
    hcalc.1 p (L p) hp.1 (exact_length_pos hp.1)
  have hqL₁ : L q = 1 := by simpa only [div_self (exact_length_pos hp.1).ne'] using hqL
  have hqUη : U q = η * L q := by
    rw [hqU, hp.2.2, hqL₁]
    field_simp [(exact_length_pos hp.1).ne']
  exact ⟨q, ⟨hq, hqS.trans hp.2.1, hqUη⟩, hqL₁, hqd, hqH⟩

/-- At an interior endpoint a locally subcritical cap gives an actual
coarsened exact problem of zero horizon. Its terminal systems are known
atlases in the original problem. -/
theorem coarsened_subcritical_horizon_zero (hinit : Initial) (hcalc : WeakCalculus) (hext : Extension)
    (S₀ η dstar δ : ℝ) (hS : 0 < S₀) (hη : 0 < η)
    (hcrit : ∀ q, AngularClass S₀ η q → 0 < Horizon q → dstar ≤ d q)
    (hδ₀ : 0 ≤ δ) (hδstar : δ < dstar) (hδ₁ : δ < 1)
    (p : Code) (hp : AngularClass S₀ η p) (a r : ℝ)
    (ha₀ : 0 ≤ a) (har : a < r) (hrL : r < L p)
    (hcap : ∀ t ∈ Icc a r, f p r - f p t ≤ δ * (r - t)) :
    ∃ q, AngularClass S₀ η q ∧ L q = r ∧ Horizon q = 0 ∧
      ∀ h, Cost q h → Known p r r h := by
  have hr₀ : 0 < r := ha₀.trans_lt har
  obtain ⟨D', hD₀, hD₁, hglobal⟩ := global_terminal_cap_of_local ha₀ har hδ₀ hδ₁
    (fun x y hx hxy hyr => exact_profile_regular hp.1 x y hx hxy (hyr.trans hrL.le)) hcap
  obtain ⟨q, hq, hqL, hqd, hqS, hqU, hprof, hKnown⟩ :=
    hcalc.2.1 p r D' hp.1 hr₀ hrL hD₀ hD₁
      (fun s hs hsr => hglobal s ⟨hs, hsr⟩)
  have hqclass : AngularClass S₀ η q := by
    refine ⟨hq, hqS.trans hp.2.1, ?_⟩
    rw [hqU, hp.2.2, hqL]
    field_simp [(exact_length_pos hp.1).ne']
  have hcapq : ∀ t ∈ Icc a (L q), f q (L q) - f q t ≤ δ * (L q - t) := by
    intro t ht
    have ht₀ := ha₀.trans ht.1
    have htr : t ≤ r := by simpa only [hqL] using ht.2
    have heqr := hprof r hr₀.le le_rfl
    have heqt := hprof t ht₀ htr
    rw [hqL]
    linarith [hcap t ⟨ht.1, htr⟩]
  have hqzero := local_subcritical_horizon_zero hinit hcalc hext S₀ η dstar δ hS hη
    hcrit hδ₀ hδstar hδ₁ q hqclass a ha₀ (by simpa only [hqL] using har) hcapq
  exact ⟨q, hqclass, hqL, hqzero, hKnown⟩

/-- The same local argument applies at the original terminal endpoint:
first replace its global density cap by the strict cap obtained from
the local interval. The chart costs do not change when the cap does. -/
theorem terminal_subcritical_horizon_zero (hinit : Initial) (hcalc : WeakCalculus) (hext : Extension)
    (S₀ η dstar δ : ℝ) (hS : 0 < S₀) (hη : 0 < η)
    (hcrit : ∀ q, AngularClass S₀ η q → 0 < Horizon q → dstar ≤ d q)
    (hδ₀ : 0 ≤ δ) (hδstar : δ < dstar) (hδ₁ : δ < 1)
    (p : Code) (hp : AngularClass S₀ η p) (a : ℝ) (ha₀ : 0 ≤ a) (ha : a < L p)
    (hcap : ∀ t ∈ Icc a (L p), f p (L p) - f p t ≤ δ * (L p - t)) :
    Horizon p = 0 := by
  obtain ⟨D', hD₀, hD₁, hglobal⟩ := global_terminal_cap_of_local ha₀ ha hδ₀ hδ₁
    (exact_profile_regular hp.1) hcap
  let q := setCap p D'
  have hq : AngularClass S₀ η q :=
    ⟨setCap_exact p hp.1 D' hD₀ hD₁ (fun r hr hrL => hglobal r ⟨hr, hrL⟩), hp.2⟩
  exact local_subcritical_horizon_zero hinit hcalc hext S₀ η dstar δ hS hη hcrit
    hδ₀ hδstar hδ₁ q hq a ha₀ ha hcap

/-- Zero coarsened cost and normalization give the exact obstruction
used in `maximizing_profiles_uniformly_linear`. -/
theorem local_subcritical_original_horizon_bound
    (hinit : Initial) (hcalc : WeakCalculus) (hext : Extension)
    (S₀ η dstar δ B : ℝ) (hS : 0 < S₀) (hη : 0 < η)
    (hcrit : ∀ q, AngularClass S₀ η q → 0 < Horizon q → dstar ≤ d q)
    (hδ₀ : 0 ≤ δ) (hδstar : δ < dstar) (hδ₁ : δ < 1)
    (p : Code) (hp : AngularClass S₀ η p)
    (hrate : ∀ q, AngularClass S₀ η q → d q ≤ d p → Horizon q ≤ B * L q)
    (a r : ℝ) (ha₀ : 0 ≤ a) (har : a < r) (hrL : r ≤ L p)
    (hcap : ∀ t ∈ Icc a r, f p r - f p t ≤ δ * (r - t)) :
    Horizon p ≤ B * (L p - r) := by
  rcases hrL.eq_or_lt with heq | hrL
  · subst r
    rw [terminal_subcritical_horizon_zero hinit hcalc hext S₀ η dstar δ hS hη
      hcrit hδ₀ hδstar hδ₁ p hp a ha₀ har hcap]
    simp
  · obtain ⟨q, hqclass, hqL, hqzero, hKnown⟩ :=
      coarsened_subcritical_horizon_zero hinit hcalc hext S₀ η dstar δ hS hη hcrit
        hδ₀ hδstar hδ₁ p hp a r ha₀ har hrL hcap
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨h, hh, hsmall⟩ := exists_lt_of_csInf_lt
      (show {h : ℝ | Cost q h}.Nonempty from ⟨L q, hinit q hqclass.1⟩)
      (show Horizon q < ε by simpa only [hqzero] using hε)
    obtain ⟨q', hq', hq'L, hq'd, hq'S, hq'U, hH, hprof, heq⟩ :=
      hcalc.2.2 p r r h (d p) hp.1 (ha₀.trans_lt har).le hrL le_rfl hrL.le
        (exact_dimension_bounds hp.1).1 (exact_dimension_bounds hp.1).2
        (fun s hrs hsL => exact_terminal_cap hp.1 s ((ha₀.trans_lt har).le.trans hrs) hsL)
        (hKnown h hh)
    have hq'class : AngularClass S₀ η q' := by
      refine ⟨hq', hq'S.trans hp.2.1, ?_⟩
      rw [hq'U, hp.2.2, hq'L]
      field_simp [(exact_length_pos hp.1).ne']
    have htail := hrate q' hq'class hq'd.le
    rw [hq'L] at htail
    linarith

end

end Submission.Obl.k4_scalar_linear_critical_extremizers.Split
