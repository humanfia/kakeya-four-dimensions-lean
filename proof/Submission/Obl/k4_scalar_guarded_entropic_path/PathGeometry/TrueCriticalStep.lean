/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrueCriticalStep.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueNormalization
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.LiteralCoarsening

/-! Critical steps normalized through their actual chosen true atlases.
The numerical maximizing-family estimates use the existing original-unit
critical step argument; the source coarsening is the literal same-law one. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- A critical step with the chosen TRUE atlas retained alongside each
literal refinement of its actual remaining exact problem. -/
structure TrueCriticalStep (ctx : CriticalContext) (source : MaximizingFamily ctx) (θ : ℝ)
    extends CriticalStep ctx source θ where
  normalizations : ∀ᶠ i in atTop,
    Nonempty (TrueNormalization (source.problem i) (remaining.problem i)
      (depth i) (depth i) (cost i))

/-- Literal same-law coarsening and tracked chosen-atlas normalization
produce a genuine true step with the same critical limits. -/
theorem nonempty_trueCriticalStep (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    Nonempty (TrueCriticalStep ctx source θ) := by
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
  have hvalid : ∀ᶠ i in atTop, 0 < depth i ∧ depth i < L (p i) ∧
      0 ≤ δ i ∧ δ i ≤ ctx.D i ∧ ∀ t ∈ Icc 0 (depth i),
        f (p i) (depth i) - f (p i) t ≤ δ i * (depth i - t) := by
    filter_upwards [hdepthpos] with i hi
    exact ⟨hi, hdepthlt i, hδ₀ i, hδD i, hcap i⟩
  obtain ⟨cost, hcost, hcostlim⟩ := exists_literal_coarsened_costs hcalc ctx source
    depth δ (θ * source.length) hdepthlim hvalid
  let outer := fun i => literalCoarsen (p i) (depth i) (δ i)
  have houter : ∀ᶠ i in atTop,
      AngularClass ctx.S₀ ctx.η (outer i) ∧ L (outer i) = depth i ∧
      d (outer i) = δ i ∧
      (∀ s ∈ Icc 0 (depth i), f (outer i) s - f (outer i) 0 = f (p i) s - f (p i) 0) := by
    filter_upwards [hvalid] with i hi
    exact ⟨(literal_coarsen_bounds hcalc ctx source i _ _
      hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2).1, rfl, rfl, fun _ _ => rfl⟩
  have houterlim : Tendsto (fun i => Horizon (outer i)) atTop
      (𝓝 (ctx.κ * (θ * source.length))) :=
    literal_coarsen_horizon_limit hcalc ctx source depth δ _ hdepthlim hvalid
  have hknown : ∀ᶠ i in atTop, TrueKnown (p i) (depth i) (depth i) (cost i) :=
    hcost.mono fun i hi => (literal_cost_iff (p i) (depth i) (δ i) (cost i)).mp hi
  have htailLength : Tendsto (fun i => L (p i) - depth i) atTop
      (𝓝 ((1 - θ) * source.length)) := by
    convert source.length_limit.sub hdepthlim using 2
    ring
  have hremainingChoose (i : ℕ) (hi : TrueKnown (p i) (depth i) (depth i) (cost i)) :
      ∃ q : Code, AngularClass ctx.S₀ ctx.η q ∧ L q = L (p i) - depth i ∧
        d q = ctx.D i ∧ Nonempty (TrueNormalization (p i) q (depth i) (depth i) (cost i)) ∧
        (∀ s ∈ Icc 0 (L q), f q s - f q 0 = f (p i) (depth i + s) - f (p i) (depth i)) ∧
        Horizon (p i) ≤ cost i + Horizon q ∧ Horizon q ≤ ctx.B i * L q := by
    obtain ⟨q, hcert, hq, hqL, hqd, hqS, hqU, hH, hprof, heq, hzero⟩ :=
      exists_true_normalization (source.angular i).1 hi (hdepth i).1 (hdepthlt i)
        le_rfl (hdepthlt i).le (hD₀ i) (ctx.cap_bounds i).2
        (fun s hrs hsL => (exact_terminal_cap (source.angular i).1 s
          ((hdepth i).1.trans hrs) hsL).trans
          (mul_le_mul_of_nonneg_right (source.cap i) (sub_nonneg.mpr hsL)))
    have hqclass : AngularClass ctx.S₀ ctx.η q := by
      refine ⟨hq, hqS.trans (source.angular i).2.1, ?_⟩
      rw [hqU, (source.angular i).2.2, hqL]
      change ctx.η * L (p i) * (L (p i) - depth i) / L (p i) =
        ctx.η * (L (p i) - depth i)
      field_simp [(hLp i).ne']
    exact ⟨q, hqclass, hqL, hqd, hcert, (fun s hs => heq rfl s hs.1 hs.2), hH,
      ctx.compare i q hqclass hqd.le⟩
  let q : ℕ → Code := fun i =>
    if hi : TrueKnown (p i) (depth i) (depth i) (cost i) then
      Classical.choose (hremainingChoose i hi) else p i
  have hq : ∀ᶠ i in atTop,
      AngularClass ctx.S₀ ctx.η (q i) ∧ L (q i) = L (p i) - depth i ∧
      d (q i) = ctx.D i ∧ Nonempty (TrueNormalization (p i) (q i) (depth i) (depth i) (cost i)) ∧
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
  let node : CriticalStep ctx source θ :=
    ⟨depth, cost, outer, remaining, rfl, hdepth, hdepthlim, hcostlim,
      houterlim, houterRate, by
        filter_upwards [houter, hcost, hq] with i ho hc hrem
        obtain ⟨cert⟩ := hrem.2.2.2.1
        exact ⟨(hdepth i).1, hdepthlt i, ho.1.1, ho.2.1, ho.2.2.1, ho.2.2.2,
          hc, Submission.Obl.k4_scalar_chart_normalization.coarsen_cost_known
            (p i) (depth i) (δ i) (cost i) hc,
          hrem.2.1, refinement_iff_nonempty_witness.mpr ⟨cert.witness⟩,
          hrem.2.2.2.2.1, hrem.2.2.2.2.2.1⟩⟩
  exact ⟨⟨node, hq.mono fun _ hi => hi.2.2.2.1⟩⟩

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
