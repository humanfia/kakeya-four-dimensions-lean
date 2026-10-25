/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/CoarsenedMaximizers.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

/-!
Coarsening actual critical problems preserves their maximizing horizon
rate. These arguments use the accepted o133 interfaces and leave the
geometric chart calculus explicit.
-/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- A terminal-known atlas pays at least the original horizon minus the
largest possible cost of its remaining problem. -/
theorem known_cost_lower_bound (hcalc : WeakCalculus)
    (S₀ η D B : ℝ) (p : Code) (hp : AngularClass S₀ η p)
    (hD₀ : 0 ≤ D) (hD₁ : D < 1) (hpd : d p ≤ D)
    (hrate : ∀ q, AngularClass S₀ η q → d q ≤ D → Horizon q ≤ B * L q)
    (r h : ℝ) (hr₀ : 0 ≤ r) (hrL : r < L p) (hKnown : Known p r r h) :
    Horizon p - B * (L p - r) ≤ h := by
  obtain ⟨q, hq, hqL, hqd, hqS, hqU, hH, hprof, heq⟩ :=
    hcalc.2.2 p r r h D hp.1 hr₀ hrL le_rfl hrL.le hD₀ hD₁
      (fun s hrs hsL =>
        (exact_terminal_cap hp.1 s (hr₀.trans hrs) hsL).trans
          (mul_le_mul_of_nonneg_right hpd (sub_nonneg.mpr hsL))) hKnown
  have hqclass : AngularClass S₀ η q := by
    refine ⟨hq, hqS.trans hp.2.1, ?_⟩
    rw [hqU, hp.2.2, hqL]
    field_simp [(exact_length_pos hp.1).ne']
  have htail := hrate q hqclass hqd.le
  rw [hqL] at htail
  linarith

/-- The coarsened exact problem has a horizon sandwiched by the actual
parent cost and the common class rate. Infima need not be attained. -/
theorem exists_coarsened_horizon_sandwich (hinit : Initial) (hcalc : WeakCalculus)
    (S₀ η D B : ℝ) (p : Code) (hp : AngularClass S₀ η p)
    (hD₀ : 0 ≤ D) (hD₁ : D < 1) (hpd : d p ≤ D)
    (hrate : ∀ q, AngularClass S₀ η q → d q ≤ D → Horizon q ≤ B * L q)
    (r δ : ℝ) (hr₀ : 0 < r) (hrL : r < L p)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1) (hδD : δ ≤ D)
    (hcap : ∀ s ∈ Icc 0 r, f p r - f p s ≤ δ * (r - s)) :
    ∃ q : Code, AngularClass S₀ η q ∧ L q = r ∧ d q = δ ∧
      (∀ s ∈ Icc 0 r, f q s - f q 0 = f p s - f p 0) ∧
      (∀ h, Cost q h → Known p r r h) ∧
      Horizon p - B * (L p - r) ≤ Horizon q ∧ Horizon q ≤ B * r := by
  obtain ⟨q, hq, hqL, hqd, hqS, hqU, hprof, hKnown⟩ :=
    hcalc.2.1 p r δ hp.1 hr₀ hrL hδ₀ hδ₁ (fun s hs hsr => hcap s ⟨hs, hsr⟩)
  have hqclass : AngularClass S₀ η q := by
    refine ⟨hq, hqS.trans hp.2.1, ?_⟩
    rw [hqU, hp.2.2, hqL]
    field_simp [(exact_length_pos hp.1).ne']
  refine ⟨q, hqclass, hqL, hqd, (fun s hs => hprof s hs.1 hs.2), hKnown, ?_, ?_⟩
  · apply le_csInf ⟨L q, hinit q hq⟩
    intro h hh
    exact known_cost_lower_bound hcalc S₀ η D B p hp hD₀ hD₁ hpd hrate
      r h hr₀.le hrL (hKnown h hh)
  · simpa only [hqL] using hrate q hqclass (hqd ▸ hδD)

/-- Actual coarsened problems stay maximizing after division by their
individual lengths. A finite initial segment may be discarded. -/
theorem exists_coarsened_maximizing_sequence (hinit : Initial) (hcalc : WeakCalculus)
    (S₀ η κ r : ℝ) (p : ℕ → Code) (D B depth δ : ℕ → ℝ)
    (hp : ∀ i, AngularClass S₀ η (p i)) (hL : ∀ i, L (p i) = 1)
    (hD₀ : ∀ i, 0 ≤ D i) (hD₁ : ∀ i, D i < 1) (hpd : ∀ i, d (p i) ≤ D i)
    (hδ₀ : ∀ i, 0 ≤ δ i) (hδ₁ : ∀ i, δ i < 1) (hδD : ∀ i, δ i ≤ D i)
    (hr₀ : 0 < r) (hr₁ : r < 1)
    (hdepth : ∀ i, depth i ∈ Icc 0 r) (hdepthlim : Tendsto depth atTop (𝓝 r))
    (hcap : ∀ i s, s ∈ Icc 0 (depth i) →
      f (p i) (depth i) - f (p i) s ≤ δ i * (depth i - s))
    (hrate : ∀ i q, AngularClass S₀ η q → d q ≤ D i → Horizon q ≤ B i * L q)
    (hHlim : Tendsto (fun i => Horizon (p i)) atTop (𝓝 κ))
    (hBlim : Tendsto B atTop (𝓝 κ)) :
    ∃ q : ℕ → Code,
      (∀ᶠ i in atTop, AngularClass S₀ η (q i) ∧ L (q i) = depth i ∧ d (q i) = δ i ∧
        (∀ s ∈ Icc 0 (depth i), f (q i) s - f (q i) 0 = f (p i) s - f (p i) 0) ∧
        (∀ h, Cost (q i) h → Known (p i) (depth i) (depth i) h)) ∧
      Tendsto (fun i => Horizon (q i)) atTop (𝓝 (κ * r)) ∧
      Tendsto (fun i => Horizon (q i) / L (q i)) atTop (𝓝 κ) := by
  classical
  have hpos : ∀ᶠ i in atTop, 0 < depth i :=
    tendsto_const_nhds.eventually_lt hdepthlim hr₀
  have hchoose (i : ℕ) (hi : 0 < depth i) :=
    exists_coarsened_horizon_sandwich hinit hcalc S₀ η (D i) (B i) (p i) (hp i)
      (hD₀ i) (hD₁ i) (hpd i) (hrate i) (depth i) (δ i) hi
      (by simpa only [hL i] using (hdepth i).2.trans_lt hr₁)
      (hδ₀ i) (hδ₁ i) (hδD i) (hcap i)
  let q : ℕ → Code := fun i =>
    if hi : 0 < depth i then Classical.choose (hchoose i hi) else p i
  have hq : ∀ᶠ i in atTop,
      AngularClass S₀ η (q i) ∧ L (q i) = depth i ∧ d (q i) = δ i ∧
      (∀ s ∈ Icc 0 (depth i), f (q i) s - f (q i) 0 = f (p i) s - f (p i) 0) ∧
      (∀ h, Cost (q i) h → Known (p i) (depth i) (depth i) h) ∧
      Horizon (p i) - B i * (1 - depth i) ≤ Horizon (q i) ∧
      Horizon (q i) ≤ B i * depth i := by
    filter_upwards [hpos] with i hi
    simpa only [q, dite_eq_left hi, hL i] using Classical.choose_spec (hchoose i hi)
  have hlo : Tendsto (fun i => Horizon (p i) - B i * (1 - depth i))
      atTop (𝓝 (κ * r)) := by
    convert hHlim.sub (hBlim.mul (tendsto_const_nhds.sub hdepthlim)) using 2
    ring
  have hlim : Tendsto (fun i => Horizon (q i)) atTop (𝓝 (κ * r)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo (hBlim.mul hdepthlim)
      (hq.mono fun i hi => hi.2.2.2.2.2.1) (hq.mono fun i hi => hi.2.2.2.2.2.2)
  refine ⟨q, hq.mono (fun i hi => ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1,
    hi.2.2.2.2.1⟩), hlim, ?_⟩
  have hlength : Tendsto (fun i => L (q i)) atTop (𝓝 r) :=
    hdepthlim.congr' (hq.mono fun i hi => hi.2.1.symm)
  have hdiv := hlim.div hlength hr₀.ne'
  rw [mul_div_cancel_right₀ _ hr₀.ne'] at hdiv
  exact hdiv.congr' (Eventually.of_forall fun _ => rfl)

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
