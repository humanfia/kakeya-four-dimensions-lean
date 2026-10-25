/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/MovingNode.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.MovingDepths

/-!
A critical node constructed in original exponent units, without replacing
the remaining exact problem by an opaque rescaling. This form can be
iterated while retaining each actual original-law refinement.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The common dimension buffers and class-rate envelopes along a critical
family. These remain fixed throughout a finite path. -/
structure CriticalContext where
  S₀ : ℝ
  η : ℝ
  dstar : ℝ
  κ : ℝ
  D : ℕ → ℝ
  B : ℕ → ℝ
  star_nonneg : 0 ≤ dstar
  star_lt_one : dstar < 1
  cap_bounds : ∀ i, dstar < D i ∧ D i < 1
  rate_limit : Tendsto B atTop (𝓝 κ)
  compare : ∀ i q, AngularClass S₀ η q → d q ≤ D i → Horizon q ≤ B i * L q

/-- A maximizing family in its actual exponent units. Its lengths may vary
with the outer index, and its relative profile errors are little-o of the
same dimension buffer used by the original family. -/
structure MaximizingFamily (ctx : CriticalContext) where
  problem : ℕ → Code
  length : ℝ
  length_pos : 0 < length
  angular : ∀ i, AngularClass ctx.S₀ ctx.η (problem i)
  cap : ∀ i, d (problem i) ≤ ctx.D i
  length_limit : Tendsto (fun i => L (problem i)) atTop (𝓝 length)
  horizon_limit : Tendsto (fun i => Horizon (problem i)) atTop (𝓝 (ctx.κ * length))
  profile_buffer : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
    ∀ s ∈ Icc (0 : ℝ) (L (problem i)),
      |f (problem i) s - f (problem i) 0 - ctx.dstar * s| ≤ ε * (ctx.D i - ctx.dstar)

/-- All witnesses at one layer of the path. The `Refinement` field retains
the full assigned priors, selected incidence laws and mixture weights. -/
structure LayerAt (p outer remaining : Code) (depth cost δ : ℝ) : Prop where
  depth_nonneg : 0 ≤ depth
  depth_lt : depth < L p
  outer_exact : Exact outer
  outer_length : L outer = depth
  outer_cap : d outer = δ
  outer_profile : ∀ s ∈ Icc 0 depth, f outer s - f outer 0 = f p s - f p 0
  outer_cost : Cost outer cost
  known : Known p depth depth cost
  remaining_length : L remaining = L p - depth
  refinement : Refinement p remaining depth depth cost
  remaining_profile : ∀ s ∈ Icc 0 (L remaining),
    f remaining s - f remaining 0 = f p (depth + s) - f p depth
  composition : Horizon p ≤ cost + Horizon remaining

/-- One actual split of a maximizing family, including all horizon limits
and the remaining maximizing family in the same original units. -/
structure CriticalStep (ctx : CriticalContext) (source : MaximizingFamily ctx) (θ : ℝ) where
  depth : ℕ → ℝ
  cost : ℕ → ℝ
  outer : ℕ → Code
  remaining : MaximizingFamily ctx
  remaining_length : remaining.length = (1 - θ) * source.length
  depth_bounds : ∀ i, depth i ∈ Icc 0 (θ * L (source.problem i))
  depth_limit : Tendsto depth atTop (𝓝 (θ * source.length))
  cost_limit : Tendsto cost atTop (𝓝 (ctx.κ * (θ * source.length)))
  outer_horizon_limit : Tendsto (fun i => Horizon (outer i)) atTop
    (𝓝 (ctx.κ * (θ * source.length)))
  outer_rate_limit : Tendsto (fun i => Horizon (outer i) / L (outer i)) atTop (𝓝 ctx.κ)
  layers : ∀ᶠ i in atTop,
    LayerAt (source.problem i) (outer i) (remaining.problem i) (depth i) (cost i)
      (ctx.dstar + (ctx.D i - ctx.dstar) / 2)

/-- A fractional node preserves the maximizing rate and the dimension
buffer without changing the units of the remaining original-law witness. -/
theorem nonempty_criticalStep (hinit : Initial) (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    Nonempty (CriticalStep ctx source θ) := by
  classical
  let p := source.problem
  have hLp (i : ℕ) : 0 < L (p i) := exact_length_pos (source.angular i).1
  let δ := fun i => ctx.dstar + (ctx.D i - ctx.dstar) / 2
  have hD₀ (i : ℕ) : 0 ≤ ctx.D i := ctx.star_nonneg.trans (ctx.cap_bounds i).1.le
  have hδ₀ (i : ℕ) : 0 ≤ δ i := by
    dsimp only [δ]
    linarith [ctx.star_nonneg, (ctx.cap_bounds i).1]
  have hδD (i : ℕ) : δ i ≤ ctx.D i := by
    dsimp only [δ]
    linarith [(ctx.cap_bounds i).1]
  have hδ₁ (i : ℕ) : δ i < 1 := (hδD i).trans_lt (ctx.cap_bounds i).2
  obtain ⟨depth, hdepth, hdepthlt, hdepthlim, hdepthpos, hcap⟩ :=
    exists_fractional_critical_depths hcalc p ctx.dstar θ source.length
      (fun i => ctx.D i - ctx.dstar) (fun i => (source.angular i).1)
      ctx.star_nonneg ctx.star_lt_one.le hθ₀ hθ₁ source.length_pos
      source.length_limit (fun i => sub_pos.mpr (ctx.cap_bounds i).1)
      source.profile_buffer
  have houterChoose (i : ℕ) (hi : 0 < depth i) :=
    exists_coarsened_horizon_sandwich hinit (weakCalculus_of_calculus hcalc)
      ctx.S₀ ctx.η (ctx.D i) (ctx.B i) (p i) (source.angular i)
      (hD₀ i) (ctx.cap_bounds i).2 (source.cap i) (ctx.compare i)
      (depth i) (δ i) hi (hdepthlt i) (hδ₀ i) (hδ₁ i) (hδD i) (hcap i)
  let outer : ℕ → Code := fun i =>
    if hi : 0 < depth i then Classical.choose (houterChoose i hi) else p i
  have houter : ∀ᶠ i in atTop,
      AngularClass ctx.S₀ ctx.η (outer i) ∧ L (outer i) = depth i ∧
      d (outer i) = δ i ∧
      (∀ s ∈ Icc 0 (depth i), f (outer i) s - f (outer i) 0 = f (p i) s - f (p i) 0) ∧
      (∀ h, Cost (outer i) h → Known (p i) (depth i) (depth i) h) ∧
      Horizon (p i) - ctx.B i * (L (p i) - depth i) ≤ Horizon (outer i) ∧
      Horizon (outer i) ≤ ctx.B i * depth i := by
    filter_upwards [hdepthpos] with i hi
    simpa only [outer, dite_eq_left hi] using Classical.choose_spec (houterChoose i hi)
  have htailLength : Tendsto (fun i => L (p i) - depth i) atTop
      (𝓝 ((1 - θ) * source.length)) := by
    convert source.length_limit.sub hdepthlim using 2
    ring
  have hlower : Tendsto (fun i => Horizon (p i) - ctx.B i * (L (p i) - depth i))
      atTop (𝓝 (ctx.κ * (θ * source.length))) := by
    convert source.horizon_limit.sub (ctx.rate_limit.mul htailLength) using 2
    ring
  have houterlim : Tendsto (fun i => Horizon (outer i)) atTop
      (𝓝 (ctx.κ * (θ * source.length))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower (ctx.rate_limit.mul hdepthlim)
      (houter.mono fun i hi => hi.2.2.2.2.2.1)
      (houter.mono fun i hi => hi.2.2.2.2.2.2)
  obtain ⟨cost, hcost, hcostlim⟩ := exists_costs_tendsto hinit outer
    (ctx.κ * (θ * source.length)) (houter.mono fun i hi => hi.1.1) houterlim
  have hknown : ∀ᶠ i in atTop, Known (p i) (depth i) (depth i) (cost i) := by
    filter_upwards [houter, hcost] with i hi hc
    exact hi.2.2.2.2.1 _ hc
  have hremainingChoose (i : ℕ) (hi : Known (p i) (depth i) (depth i) (cost i)) :
      ∃ q : Code, AngularClass ctx.S₀ ctx.η q ∧ L q = L (p i) - depth i ∧
        d q = ctx.D i ∧ Refinement (p i) q (depth i) (depth i) (cost i) ∧
        (∀ s ∈ Icc 0 (L q), f q s - f q 0 = f (p i) (depth i + s) - f (p i) (depth i)) ∧
        Horizon (p i) ≤ cost i + Horizon q ∧ Horizon q ≤ ctx.B i * L q := by
    obtain ⟨q, hq, hqL, hqd, hqS, hqU, href, hH, hprof, heq⟩ :=
      hcalc.2.2 (p i) (depth i) (depth i) (cost i) (ctx.D i)
        (source.angular i).1 (hdepth i).1 (hdepthlt i) le_rfl (hdepthlt i).le
        (hD₀ i) (ctx.cap_bounds i).2
        (fun s hrs hsL => (exact_terminal_cap (source.angular i).1 s
          ((hdepth i).1.trans hrs) hsL).trans
          (mul_le_mul_of_nonneg_right (source.cap i) (sub_nonneg.mpr hsL))) hi
    have hqclass : AngularClass ctx.S₀ ctx.η q := by
      refine ⟨hq, hqS.trans (source.angular i).2.1, ?_⟩
      rw [hqU, (source.angular i).2.2, hqL]
      change ctx.η * L (p i) * (L (p i) - depth i) / L (p i) =
        ctx.η * (L (p i) - depth i)
      field_simp [(hLp i).ne']
    exact ⟨q, hqclass, hqL, hqd, href, (fun s hs => heq rfl s hs.1 hs.2), hH,
      ctx.compare i q hqclass hqd.le⟩
  let q : ℕ → Code := fun i =>
    if hi : Known (p i) (depth i) (depth i) (cost i) then
      Classical.choose (hremainingChoose i hi) else p i
  have hq : ∀ᶠ i in atTop,
      AngularClass ctx.S₀ ctx.η (q i) ∧ L (q i) = L (p i) - depth i ∧
      d (q i) = ctx.D i ∧ Refinement (p i) (q i) (depth i) (depth i) (cost i) ∧
      (∀ s ∈ Icc 0 (L (q i)),
        f (q i) s - f (q i) 0 = f (p i) (depth i + s) - f (p i) (depth i)) ∧
      Horizon (p i) ≤ cost i + Horizon (q i) ∧ Horizon (q i) ≤ ctx.B i * L (q i) := by
    filter_upwards [hknown] with i hi
    simpa only [q, dite_eq_left hi] using Classical.choose_spec (hremainingChoose i hi)
  have hqclass (i : ℕ) : AngularClass ctx.S₀ ctx.η (q i) := by
    dsimp only [q]
    split_ifs with hi
    · exact (Classical.choose_spec (hremainingChoose i hi)).1
    · exact source.angular i
  have hqcap (i : ℕ) : d (q i) ≤ ctx.D i := by
    dsimp only [q]
    split_ifs with hi
    · exact (Classical.choose_spec (hremainingChoose i hi)).2.2.1.le
    · exact source.cap i
  have hqLlim : Tendsto (fun i => L (q i)) atTop (𝓝 ((1 - θ) * source.length)) :=
    htailLength.congr' (hq.mono fun i hi => hi.2.1.symm)
  have hqlo : Tendsto (fun i => Horizon (p i) - cost i) atTop
      (𝓝 (ctx.κ * ((1 - θ) * source.length))) := by
    convert source.horizon_limit.sub hcostlim using 2
    ring
  have hqHlim : Tendsto (fun i => Horizon (q i)) atTop
      (𝓝 (ctx.κ * ((1 - θ) * source.length))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hqlo (ctx.rate_limit.mul hqLlim)
      (hq.mono fun i hi => by linarith [hi.2.2.2.2.2.1])
      (hq.mono fun i hi => hi.2.2.2.2.2.2)
  have hqprofile : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) (L (q i)),
      |f (q i) s - f (q i) 0 - ctx.dstar * s| ≤ ε * (ctx.D i - ctx.dstar) := by
    intro ε hε
    filter_upwards [hq, source.profile_buffer (ε / 2) (half_pos hε)] with i hi hp s hs
    have ht : depth i ∈ Icc 0 (L (p i)) := ⟨(hdepth i).1, (hdepthlt i).le⟩
    have hts : depth i + s ∈ Icc 0 (L (p i)) := by
      constructor
      · exact add_nonneg ht.1 hs.1
      · rw [hi.2.1] at hs
        linarith [hs.2]
    rw [hi.2.2.2.2.1 s hs]
    calc
      _ = |(f (p i) (depth i + s) - f (p i) 0 - ctx.dstar * (depth i + s)) -
          (f (p i) (depth i) - f (p i) 0 - ctx.dstar * depth i)| := by congr 1; ring
      _ ≤ |f (p i) (depth i + s) - f (p i) 0 - ctx.dstar * (depth i + s)| +
          |f (p i) (depth i) - f (p i) 0 - ctx.dstar * depth i| := abs_sub _ _
      _ ≤ _ := by linarith [hp _ hts, hp _ ht]
  let remaining : MaximizingFamily ctx :=
    ⟨q, (1 - θ) * source.length, mul_pos (sub_pos.mpr hθ₁) source.length_pos,
      hqclass, hqcap, hqLlim, hqHlim, hqprofile⟩
  have houterRate : Tendsto (fun i => Horizon (outer i) / L (outer i)) atTop (𝓝 ctx.κ) := by
    have hLen : Tendsto (fun i => L (outer i)) atTop (𝓝 (θ * source.length)) :=
      hdepthlim.congr' (houter.mono fun i hi => hi.2.1.symm)
    have hne : θ * source.length ≠ 0 := (mul_pos hθ₀ source.length_pos).ne'
    have hdiv := houterlim.div hLen hne
    rw [mul_div_cancel_right₀ _ hne] at hdiv
    exact hdiv.congr' (Eventually.of_forall fun _ => rfl)
  refine ⟨⟨depth, cost, outer, remaining, rfl, hdepth, hdepthlim, hcostlim,
    houterlim, houterRate, ?_⟩⟩
  filter_upwards [houter, hcost, hknown, hq] with i ho hc hk hrem
  exact ⟨(hdepth i).1, hdepthlt i, ho.1.1, ho.2.1, ho.2.2.1, ho.2.2.2.1,
    hc, hk, hrem.2.1, hrem.2.2.2.1, hrem.2.2.2.2.1, hrem.2.2.2.2.2.1⟩

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
