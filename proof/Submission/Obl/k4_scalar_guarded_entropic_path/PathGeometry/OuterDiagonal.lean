/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/OuterDiagonal.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPrefixes
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.KnownExclusion

/-!
The outer stage of the critical tangent diagonal: choose an actual exact
problem only after fixing the finite grid and its positive gain buffer.
No sample of that exact problem is selected in this construction.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Every node of a fixed finite grid has accurate original-unit depths
and costs on one common eventual outer tail. -/
theorem eventually_prefix_accuracy {ctx : CriticalContext} {source : MaximizingFamily ctx}
    (hsource : source.length = 1) {targets : List ℝ} (path : GridPath ctx source 0 targets)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ i in atTop, ∀ n : Fin (targets.length + 1),
      |(path.take n).totalDepth i - (path.take n).endpoint| < δ ∧
      |(path.take n).totalCost i - ctx.κ * (path.take n).endpoint| < δ := by
  have hbase : source.length = (1 - (0 : ℝ)) * 1 := by simpa using hsource
  apply Filter.eventually_all.2
  intro n
  have hdepth : Tendsto (path.take n).totalDepth atTop (𝓝 (path.take n).endpoint) := by
    simpa only [sub_zero, mul_one] using (path.take n).totalDepth_limit 1 hbase
  have hcost : Tendsto (path.take n).totalCost atTop (𝓝 (ctx.κ * (path.take n).endpoint)) := by
    simpa only [sub_zero, mul_one] using (path.take n).totalCost_limit 1 hbase
  filter_upwards [Metric.tendsto_nhds.1 hdepth δ hδ,
    Metric.tendsto_nhds.1 hcost δ hδ] with i hd hc
  exact ⟨by simpa only [Real.dist_eq] using hd, by simpa only [Real.dist_eq] using hc⟩

/-- The requirements imposed at a fixed outer stage, before its exact
sample and complexity guard are chosen. -/
structure OuterReady {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {targets : List ℝ} (path : GridPath ctx source 0 targets)
    (δ gain : ℝ) (extra : ℕ → Prop) (i : ℕ) : Prop where
  layers : path.AllLayers i
  prefixes : ∀ n : Fin (targets.length + 1),
    |(path.take n).totalDepth i - (path.take n).endpoint| < δ ∧
    |(path.take n).totalCost i - ctx.κ * (path.take n).endpoint| < δ
  exclusion : ∀ r b h : ℝ, 0 ≤ r → r < L (source.problem i) →
    r ≤ b → b ≤ L (source.problem i) → h ≤ ctx.κ * r - gain →
    ¬ Known (source.problem i) r b h
  additional : extra i

/-- Choose actual outer problems with all finite-grid errors, layer
witnesses and the declared gain exclusion already in force. Additional
eventual requirements may be imposed at each fixed stage. -/
theorem exists_outer_diagonal (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx) (hsource : source.length = 1)
    (targets : ℕ → List ℝ) (paths : (n : ℕ) → GridPath ctx source 0 (targets n))
    (δ gain : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hgain : ∀ n, 0 < gain n)
    (extra : ℕ → ℕ → Prop) (hextra : ∀ n, ∀ᶠ i in atTop, extra n i) :
    ∃ index : ℕ → ℕ, Tendsto index atTop atTop ∧
      ∀ n, n ≤ index n ∧ OuterReady (paths n) (δ n) (gain n) (extra n) (index n) := by
  classical
  have hready (n : ℕ) : ∀ᶠ i in atTop,
      OuterReady (paths n) (δ n) (gain n) (extra n) i := by
    filter_upwards [(paths n).eventually_allLayers,
      eventually_prefix_accuracy hsource (paths n) (δ n) (hδ n),
      eventually_no_known_gain hcalc ctx source (gain n) (hgain n), hextra n]
      with i hl hp he hx
    exact ⟨hl, hp, he, hx⟩
  have hchoose (n : ℕ) : ∃ i : ℕ,
      n ≤ i ∧ OuterReady (paths n) (δ n) (gain n) (extra n) i :=
    ((eventually_ge_atTop n).and (hready n)).exists
  choose index hindex hspec using hchoose
  refine ⟨index, ?_, fun n => ⟨hindex n, hspec n⟩⟩
  apply tendsto_atTop.2
  intro b
  exact eventually_atTop.2 ⟨b, fun n hn => hn.trans (hindex n)⟩

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
