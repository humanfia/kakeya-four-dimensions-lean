/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/RemainingMaximizers.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CoarsenedMaximizers

/-!
Near-minimal outer costs and actual remaining exact problems. The
Refinement witness retains the full assigned priors, selected laws and
original mixture weights supplied by the geometric chart calculus.
-/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Choose genuine costs converging to the limiting horizon, without
asserting that any individual horizon is attained. -/
theorem exists_costs_tendsto (hinit : Initial) (p : ℕ → Code) (a : ℝ)
    (hp : ∀ᶠ i in atTop, Exact (p i))
    (hlim : Tendsto (fun i => Horizon (p i)) atTop (𝓝 a)) :
    ∃ h : ℕ → ℝ, (∀ᶠ i in atTop, Cost (p i) (h i)) ∧ Tendsto h atTop (𝓝 a) := by
  classical
  let ε := fun i : ℕ => 1 / ((i : ℝ) + 1)
  have hε (i : ℕ) : 0 < ε i := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hchoose (i : ℕ) (hi : Exact (p i)) :
      ∃ h : ℝ, Cost (p i) h ∧ h < Horizon (p i) + ε i :=
    exists_lt_of_csInf_lt ⟨L (p i), hinit (p i) hi⟩
      (lt_add_of_pos_right _ (hε i))
  let h : ℕ → ℝ := fun i =>
    if hi : Exact (p i) then Classical.choose (hchoose i hi) else 0
  have hspec : ∀ᶠ i in atTop,
      Cost (p i) (h i) ∧ Horizon (p i) ≤ h i ∧ h i ≤ Horizon (p i) + ε i := by
    filter_upwards [hp] with i hi
    have hc := Classical.choose_spec (hchoose i hi)
    have heq : h i = Classical.choose (hchoose i hi) := by
      dsimp only [h]
      rw [dite_eq_left hi]
    rw [heq]
    exact ⟨hc.1, csInf_le ⟨0, fun _ hh => hh.1⟩ hc.1, hc.2.le⟩
  refine ⟨h, hspec.mono (fun i hi => hi.1), ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim
    (show Tendsto (fun i => Horizon (p i) + ε i) atTop (𝓝 a) by
      simpa only [add_zero] using hlim.add hεlim)
    (hspec.mono fun i hi => hi.2.1) (hspec.mono fun i hi => hi.2.2)

/-- Normalizing the original finer problem through near-optimal outer
atlases leaves a maximizing remaining sequence, with actual provenance. -/
theorem exists_remaining_maximizing_sequence (hcalc : Calculus)
    (S₀ η κ r : ℝ) (p : ℕ → Code) (D B depth h : ℕ → ℝ)
    (hp : ∀ i, AngularClass S₀ η (p i)) (hL : ∀ i, L (p i) = 1)
    (hD₀ : ∀ i, 0 ≤ D i) (hD₁ : ∀ i, D i < 1) (hpd : ∀ i, d (p i) ≤ D i)
    (hrate : ∀ i q, AngularClass S₀ η q → d q ≤ D i → Horizon q ≤ B i * L q)
    (hKnown : ∀ᶠ i in atTop, 0 ≤ depth i ∧ depth i < 1 ∧
      Known (p i) (depth i) (depth i) (h i))
    (hr₁ : r < 1) (hdepthlim : Tendsto depth atTop (𝓝 r))
    (hHlim : Tendsto (fun i => Horizon (p i)) atTop (𝓝 κ))
    (hhlim : Tendsto h atTop (𝓝 (κ * r))) (hBlim : Tendsto B atTop (𝓝 κ)) :
    ∃ q : ℕ → Code,
      (∀ᶠ i in atTop, AngularClass S₀ η (q i) ∧ L (q i) = 1 - depth i ∧
        d (q i) = D i ∧ Refinement (p i) (q i) (depth i) (depth i) (h i) ∧
        (∀ s ∈ Icc 0 (L (q i)),
          f (q i) s - f (q i) 0 = f (p i) (depth i + s) - f (p i) (depth i)) ∧
        Horizon (p i) ≤ h i + Horizon (q i)) ∧
      Tendsto (fun i => Horizon (q i)) atTop (𝓝 (κ * (1 - r))) ∧
      Tendsto (fun i => Horizon (q i) / L (q i)) atTop (𝓝 κ) := by
  classical
  let Good := fun i => 0 ≤ depth i ∧ depth i < 1 ∧
    Known (p i) (depth i) (depth i) (h i)
  have hchoose (i : ℕ) (hi : Good i) :
      ∃ q : Code, AngularClass S₀ η q ∧ L q = 1 - depth i ∧ d q = D i ∧
        Refinement (p i) q (depth i) (depth i) (h i) ∧
        (∀ s ∈ Icc 0 (L q), f q s - f q 0 =
          f (p i) (depth i + s) - f (p i) (depth i)) ∧
        Horizon (p i) ≤ h i + Horizon q ∧ Horizon q ≤ B i * (1 - depth i) := by
    obtain ⟨q, hq, hqL, hqd, hqS, hqU, href, hH, hprof, heq⟩ :=
      hcalc.2.2 (p i) (depth i) (depth i) (h i) (D i) (hp i).1 hi.1
        (by simpa only [hL i] using hi.2.1) le_rfl
        (by simpa only [hL i] using hi.2.1.le) (hD₀ i) (hD₁ i)
        (fun s hrs hsL =>
          (exact_terminal_cap (hp i).1 s (hi.1.trans hrs) hsL).trans
            (mul_le_mul_of_nonneg_right (hpd i) (sub_nonneg.mpr hsL))) hi.2.2
    have hqclass : AngularClass S₀ η q := by
      refine ⟨hq, hqS.trans (hp i).2.1, ?_⟩
      rw [hqU, (hp i).2.2, hqL]
      field_simp [(exact_length_pos (hp i).1).ne']
    have hqL' : L q = 1 - depth i := by simpa only [hL i] using hqL
    refine ⟨q, hqclass, hqL', hqd, href, ?_, hH, ?_⟩
    · intro s hs
      exact heq rfl s hs.1 hs.2
    · simpa only [hqL'] using hrate i q hqclass hqd.le
  let q : ℕ → Code := fun i =>
    if hi : Good i then Classical.choose (hchoose i hi) else p i
  have hq : ∀ᶠ i in atTop,
      AngularClass S₀ η (q i) ∧ L (q i) = 1 - depth i ∧ d (q i) = D i ∧
      Refinement (p i) (q i) (depth i) (depth i) (h i) ∧
      (∀ s ∈ Icc 0 (L (q i)), f (q i) s - f (q i) 0 =
        f (p i) (depth i + s) - f (p i) (depth i)) ∧
      Horizon (p i) ≤ h i + Horizon (q i) ∧ Horizon (q i) ≤ B i * (1 - depth i) := by
    filter_upwards [hKnown] with i hi
    change Good i at hi
    simpa only [q, dite_eq_left hi] using Classical.choose_spec (hchoose i hi)
  have hlo : Tendsto (fun i => Horizon (p i) - h i) atTop (𝓝 (κ * (1 - r))) := by
    convert hHlim.sub hhlim using 2
    ring
  have hlength' : Tendsto (fun i => 1 - depth i) atTop (𝓝 (1 - r)) :=
    tendsto_const_nhds.sub hdepthlim
  have hlim : Tendsto (fun i => Horizon (q i)) atTop (𝓝 (κ * (1 - r))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo (hBlim.mul hlength')
      (hq.mono fun i hi => by linarith [hi.2.2.2.2.2.1])
      (hq.mono fun i hi => hi.2.2.2.2.2.2)
  refine ⟨q, hq.mono (fun i hi => ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1,
    hi.2.2.2.2.1, hi.2.2.2.2.2.1⟩), hlim, ?_⟩
  have hlength : Tendsto (fun i => L (q i)) atTop (𝓝 (1 - r)) :=
    hlength'.congr' (hq.mono fun i hi => hi.2.1.symm)
  have hne : 1 - r ≠ 0 := sub_ne_zero.mpr hr₁.ne'
  have hdiv := hlim.div hlength hne
  rw [mul_div_cancel_right₀ _ hne] at hdiv
  exact hdiv.congr' (Eventually.of_forall fun _ => rfl)

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
