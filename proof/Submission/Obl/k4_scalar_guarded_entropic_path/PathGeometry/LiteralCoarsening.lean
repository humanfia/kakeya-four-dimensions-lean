/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/LiteralCoarsening.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.KnownExclusion
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PrefixCaps
import Submission.Obl.k4_scalar_chart_normalization.Coarsening
import Submission.Obl.k4_scalar_initial_true_horizon

/-! Near-optimal true costs on the literal same-law coarsenings of critical families. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- This coarsening keeps the original worlds, priors, events and weights. -/
noncomputable def literalCoarsen (p : Code) (r δ : ℝ) : Code :=
  Submission.Obl.k4_scalar_chart_normalization.coarsen p r δ

/-- Its true charts are literally charts on the original laws at depth r. -/
theorem literal_cost_iff (p : Code) (r δ h : ℝ) :
    Cost (literalCoarsen p r δ) h ↔
      0 ≤ h ∧ ∃ B : ℕ, 1 ≤ B ∧ ∀ ε : ℝ, 0 < ε →
        ∃ᶠ k in atTop, Chart p B r r (h + ε) ε true k := Iff.rfl

/-- Actual same-law coarsenings satisfy the critical horizon sandwiches.
Their own true costs become original known costs by the accepted map. -/
theorem literal_coarsen_bounds (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx) (i : ℕ)
    (r δ : ℝ) (hr : 0 < r) (hrL : r < L (source.problem i))
    (hδ : 0 ≤ δ) (hδD : δ ≤ ctx.D i)
    (hcap : ∀ t ∈ Icc 0 r,
      f (source.problem i) r - f (source.problem i) t ≤ δ * (r - t)) :
    AngularClass ctx.S₀ ctx.η (literalCoarsen (source.problem i) r δ) ∧
      ctx.κ * r - exclusionError ctx source i ≤
        Horizon (literalCoarsen (source.problem i) r δ) ∧
      Horizon (literalCoarsen (source.problem i) r δ) ≤ ctx.B i * r := by
  let q := literalCoarsen (source.problem i) r δ
  have hp := (source.angular i).1
  have hq : Exact q := Submission.Obl.k4_scalar_chart_normalization.exact_coarsen hp hr hrL
    hδ (hδD.trans_lt (ctx.cap_bounds i).2) (fun t ht htr => hcap t ⟨ht, htr⟩)
  have hclass : AngularClass ctx.S₀ ctx.η q := by
    refine ⟨hq, (source.angular i).2.1, ?_⟩
    change U (source.problem i) * r / L (source.problem i) = ctx.η * r
    rw [(source.angular i).2.2]
    field_simp [(exact_length_pos hp).ne']
  refine ⟨hclass, ?_, ?_⟩
  · apply le_csInf (show {a : ℝ | Cost q a}.Nonempty from
      ⟨L q, Submission.k4_scalar_initial_true_horizon q hq⟩)
    intro a ha
    have hk := Submission.Obl.k4_scalar_chart_normalization.coarsen_cost_known
      (source.problem i) r δ a ha
    have hb := known_gain_le_error hcalc ctx source i r r a hr.le hrL le_rfl hrL.le hk
    linarith
  · exact ctx.compare i q hclass hδD

/-- Moving original depths have the same limiting critical horizon in
the literal coarsened problems. Finite invalid initial indices are ignored. -/
theorem literal_coarsen_horizon_limit (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx)
    (depth cap : ℕ → ℝ) (R : ℝ) (hdepth : Tendsto depth atTop (𝓝 R))
    (hvalid : ∀ᶠ i in atTop, 0 < depth i ∧ depth i < L (source.problem i) ∧
      0 ≤ cap i ∧ cap i ≤ ctx.D i ∧
      ∀ t ∈ Icc 0 (depth i),
        f (source.problem i) (depth i) - f (source.problem i) t ≤ cap i * (depth i - t)) :
    Tendsto (fun i => Horizon (literalCoarsen (source.problem i) (depth i) (cap i)))
      atTop (𝓝 (ctx.κ * R)) := by
  have hlo : Tendsto (fun i => ctx.κ * depth i - exclusionError ctx source i)
      atTop (𝓝 (ctx.κ * R)) := by
    simpa only [sub_zero] using
      (hdepth.const_mul ctx.κ).sub (exclusionError_tendsto ctx source)
  have hhi := ctx.rate_limit.mul hdepth
  have hb : ∀ᶠ i in atTop,
      ctx.κ * depth i - exclusionError ctx source i ≤
          Horizon (literalCoarsen (source.problem i) (depth i) (cap i)) ∧
      Horizon (literalCoarsen (source.problem i) (depth i) (cap i)) ≤ ctx.B i * depth i := by
    filter_upwards [hvalid] with i hi
    exact (literal_coarsen_bounds hcalc ctx source i _ _
      hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2).2
  exact hlo.squeeze' hhi (hb.mono fun _ hi => hi.1) (hb.mono fun _ hi => hi.2)

/-- Genuine attainable TRUE costs at the actual depths, on the literal
original-law coarsenings, approach the critical time. -/
theorem exists_literal_coarsened_costs (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx)
    (depth cap : ℕ → ℝ) (R : ℝ) (hdepth : Tendsto depth atTop (𝓝 R))
    (hvalid : ∀ᶠ i in atTop, 0 < depth i ∧ depth i < L (source.problem i) ∧
      0 ≤ cap i ∧ cap i ≤ ctx.D i ∧
      ∀ t ∈ Icc 0 (depth i),
        f (source.problem i) (depth i) - f (source.problem i) t ≤ cap i * (depth i - t)) :
    ∃ cost : ℕ → ℝ,
      (∀ᶠ i in atTop, Cost (literalCoarsen (source.problem i) (depth i) (cap i)) (cost i)) ∧
      Tendsto cost atTop (𝓝 (ctx.κ * R)) := by
  apply exists_costs_tendsto Submission.k4_scalar_initial_true_horizon _ _ ?_
    (literal_coarsen_horizon_limit hcalc ctx source depth cap R hdepth hvalid)
  filter_upwards [hvalid] with i hi
  exact (literal_coarsen_bounds hcalc ctx source i _ _
    hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2).1.1

namespace GridPath

/-- Every positive actual cumulative prefix has genuine original-law true
costs approaching its critical time, using the SAME actual depth sequence. -/
theorem exists_original_true_costs (hcalc : Calculus)
    {ctx : CriticalContext} {source : MaximizingFamily ctx} {start : ℝ} {targets : List ℝ}
    (path : GridPath ctx source start targets) (baseLength : ℝ)
    (hbase : source.length = (1 - start) * baseLength)
    (hpositive : 0 < (path.endpoint - start) * baseLength) :
    ∃ cost : ℕ → ℝ,
      (∀ᶠ i in atTop,
        Cost (literalCoarsen (source.problem i) (path.totalDepth i)
          (ctx.dstar + (ctx.D i - ctx.dstar) / 2)) (cost i)) ∧
      Tendsto cost atTop (𝓝 (ctx.κ * ((path.endpoint - start) * baseLength))) := by
  have hlim := path.totalDepth_limit baseLength hbase
  apply exists_literal_coarsened_costs hcalc ctx source _ _ _ hlim
  have hpos : ∀ᶠ i in atTop, 0 < path.totalDepth i :=
    tendsto_const_nhds.eventually_lt hlim hpositive
  filter_upwards [hpos, path.path_law, path.cumulative_endpoint_cap] with i hi hlaw hcap
  refine ⟨hi, hlaw.depth_lt, ?_, ?_, hcap⟩ <;>
    linarith [ctx.star_nonneg, (ctx.cap_bounds i).1]

end GridPath

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
