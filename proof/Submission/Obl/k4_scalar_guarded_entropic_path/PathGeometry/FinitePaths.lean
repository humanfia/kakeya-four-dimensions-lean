/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/FinitePaths.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.MovingNode

/-!
Finite ordered critical paths. Each layer stores its actual remaining
exact problem and full original-law refinement. All cumulative depths
and horizons are computed in the original exponent units.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- A finite ordered grid of actual critical splits. The fraction for
each next node is computed from the limiting remaining length. -/
inductive GridPath (ctx : CriticalContext) :
    (source : MaximizingFamily ctx) → ℝ → List ℝ → Type where
  | nil (source : MaximizingFamily ctx) (start : ℝ) : GridPath ctx source start []
  | cons {source : MaximizingFamily ctx} {start : ℝ} (r : ℝ) (rs : List ℝ)
      (hstart : start < r) (hr : r < 1)
      (node : CriticalStep ctx source ((r - start) / (1 - start)))
      (tail : GridPath ctx node.remaining r rs) : GridPath ctx source start (r :: rs)

/-- Every finite strictly ordered interior grid has an actual critical
path. Its steps use only the explicit initial horizon and chart calculus. -/
theorem nonempty_gridPath (hinit : Initial) (hcalc : Calculus)
    (ctx : CriticalContext) (source : MaximizingFamily ctx)
    (start : ℝ) (targets : List ℝ) (hstart : start < 1)
    (hordered : targets.Pairwise (· < ·))
    (htargets : ∀ r ∈ targets, start < r ∧ r < 1) :
    Nonempty (GridPath ctx source start targets) := by
  induction targets generalizing source start with
  | nil => exact ⟨.nil source start⟩
  | cons r rs ih =>
    have hr := htargets r (by simp)
    have hθ₀ : 0 < (r - start) / (1 - start) :=
      div_pos (sub_pos.mpr hr.1) (sub_pos.mpr hstart)
    have hθ₁ : (r - start) / (1 - start) < 1 := by
      apply (div_lt_one (sub_pos.mpr hstart)).2
      linarith [hr.2]
    obtain ⟨node⟩ := nonempty_criticalStep hinit hcalc ctx source _ hθ₀ hθ₁
    have hpairs := List.pairwise_cons.mp hordered
    have htail : ∀ s ∈ rs, r < s ∧ s < 1 := by
      intro s hs
      exact ⟨hpairs.1 s hs, (htargets s (by simp [hs])).2⟩
    obtain ⟨tail⟩ := ih node.remaining r hr.2 hpairs.2 htail
    exact ⟨.cons r rs hr.1 hr.2 node tail⟩

namespace GridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- The remaining exact family after all recorded layers. -/
def finalFamily {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) : MaximizingFamily ctx :=
  match path with
  | .nil source _ => source
  | .cons _ _ _ _ _ tail => finalFamily tail

/-- The last target, or the initial target if the grid is empty. -/
def endpoint {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) : ℝ :=
  match path with
  | .nil _ start => start
  | .cons _ _ _ _ _ tail => endpoint tail

/-- The sum of actual layer depths, before any length normalization. -/
def totalDepth {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) (i : ℕ) : ℝ :=
  match path with
  | .nil _ _ => 0
  | .cons _ _ _ _ node tail => node.depth i + totalDepth tail i

/-- The sum of attainable outer costs along the actual layers. -/
def totalCost {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) (i : ℕ) : ℝ :=
  match path with
  | .nil _ _ => 0
  | .cons _ _ _ _ node tail => node.cost i + totalCost tail i

/-- All layers are valid simultaneously at a fixed outer index. -/
def AllLayers {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets) (i : ℕ) : Prop :=
  match path with
  | .nil _ _ => True
  | .cons r _ _ _ node tail =>
      LayerAt (source.problem i) (node.outer i) (node.remaining.problem i)
        (node.depth i) (node.cost i) (ctx.dstar + (ctx.D i - ctx.dstar) / 2) ∧
      tail.AllLayers i

/-- A finite path requires only one eventual tail of the original outer
index, and does not interchange its outer and exact-sequence limits. -/
theorem eventually_allLayers (path : GridPath ctx source start targets) :
    ∀ᶠ i in atTop, path.AllLayers i := by
  induction path with
  | nil => exact Eventually.of_forall fun _ => trivial
  | cons r rs hstart hr node tail ih => exact node.layers.and ih

/-- The exact limiting length at every stage uses its target on the
original grid, with no replacement of termwise lengths by their limits. -/
theorem final_length (path : GridPath ctx source start targets) (baseLength : ℝ)
    (hbase : source.length = (1 - start) * baseLength) :
    path.finalFamily.length = (1 - path.endpoint) * baseLength := by
  induction path with
  | nil => exact hbase
  | @cons source start r rs hstart hr node tail ih =>
    apply ih
    rw [node.remaining_length, hbase]
    have hden : 1 - start ≠ 0 := (sub_pos.mpr (hstart.trans hr)).ne'
    field_simp [hden]
    ring

/-- The cumulative actual depths approach the prescribed grid endpoint. -/
theorem totalDepth_limit (path : GridPath ctx source start targets) (baseLength : ℝ)
    (hbase : source.length = (1 - start) * baseLength) :
    Tendsto path.totalDepth atTop (𝓝 ((path.endpoint - start) * baseLength)) := by
  induction path with
  | nil => simpa only [totalDepth, endpoint, sub_self, zero_mul] using
      (tendsto_const_nhds (x := (0 : ℝ)))
  | @cons source start r rs hstart hr node tail ih =>
    have hden : 1 - start ≠ 0 := (sub_pos.mpr (hstart.trans hr)).ne'
    have hnext : node.remaining.length = (1 - r) * baseLength := by
      rw [node.remaining_length, hbase]
      field_simp [hden]
      ring
    have hnode : (r - start) / (1 - start) * source.length = (r - start) * baseLength := by
      rw [hbase]
      field_simp [hden]
    have ht := node.depth_limit.add (ih hnext)
    rw [hnode] at ht
    change Tendsto (fun i => node.depth i + tail.totalDepth i) atTop
      (𝓝 ((tail.endpoint - start) * baseLength))
    convert ht using 2
    ring

/-- Segment costs add in the original units to the critical cost of the
whole traversed depth. -/
theorem totalCost_limit (path : GridPath ctx source start targets) (baseLength : ℝ)
    (hbase : source.length = (1 - start) * baseLength) :
    Tendsto path.totalCost atTop (𝓝 (ctx.κ * ((path.endpoint - start) * baseLength))) := by
  induction path with
  | nil => simpa only [totalCost, endpoint, sub_self, zero_mul, mul_zero] using
      (tendsto_const_nhds (x := (0 : ℝ)))
  | @cons source start r rs hstart hr node tail ih =>
    have hden : 1 - start ≠ 0 := (sub_pos.mpr (hstart.trans hr)).ne'
    have hnext : node.remaining.length = (1 - r) * baseLength := by
      rw [node.remaining_length, hbase]
      field_simp [hden]
      ring
    have hnode : (r - start) / (1 - start) * source.length = (r - start) * baseLength := by
      rw [hbase]
      field_simp [hden]
    have ht := node.cost_limit.add (ih hnext)
    rw [hnode] at ht
    change Tendsto (fun i => node.cost i + tail.totalCost i) atTop
      (𝓝 (ctx.κ * ((tail.endpoint - start) * baseLength)))
    convert ht using 2
    ring

/-- Positivity holds termwise even before the finitely many initial outer
indices at which all layer laws become available have been removed. -/
theorem totalDepth_nonneg (path : GridPath ctx source start targets) (i : ℕ) :
    0 ≤ path.totalDepth i := by
  induction path with
  | nil => exact le_rfl
  | cons r rs hstart hr node tail ih =>
    exact add_nonneg (node.depth_bounds i).1 ih

/-- The identities obtained by composing all finite layers. Each separate
layer still retains its full `Refinement` in the path itself. -/
structure PathLaw (p q : Code) (depth cost : ℝ) : Prop where
  length : L q = L p - depth
  depth_nonneg : 0 ≤ depth
  depth_lt : depth < L p
  profile : ∀ s ∈ Icc 0 (L q), f q s - f q 0 = f p (depth + s) - f p depth
  horizon : Horizon p ≤ cost + Horizon q

/-- Finite layer laws share one eventual tail; cumulative profiles and
horizon costs are transported through the actual intermediate problems. -/
theorem path_law (path : GridPath ctx source start targets) :
    ∀ᶠ i in atTop, PathLaw (source.problem i) (path.finalFamily.problem i)
      (path.totalDepth i) (path.totalCost i) := by
  induction path with
  | nil source start =>
    exact Eventually.of_forall fun i =>
      ⟨by simp [finalFamily, totalDepth], le_rfl,
        by simpa only [totalDepth] using exact_length_pos (source.angular i).1,
        by simp [finalFamily, totalDepth], by simp [finalFamily, totalCost]⟩
  | @cons source start r rs hstart hr node tail ih =>
    filter_upwards [node.layers, ih] with i hn ht
    have hlen : L (tail.finalFamily.problem i) =
        L (source.problem i) - (node.depth i + tail.totalDepth i) := by
      rw [ht.length, hn.remaining_length]
      ring
    have hpos : 0 < L (tail.finalFamily.problem i) :=
      exact_length_pos (tail.finalFamily.angular i).1
    have hdepth : node.depth i + tail.totalDepth i < L (source.problem i) := by
      linarith
    refine ⟨hlen, add_nonneg hn.depth_nonneg ht.depth_nonneg, hdepth, ?_, ?_⟩
    · intro s hs
      change s ∈ Icc 0 (L (tail.finalFamily.problem i)) at hs
      have hz : tail.totalDepth i ∈ Icc 0 (L (node.remaining.problem i)) :=
        ⟨ht.depth_nonneg, ht.depth_lt.le⟩
      have hzs : tail.totalDepth i + s ∈ Icc 0 (L (node.remaining.problem i)) := by
        constructor
        · exact add_nonneg ht.depth_nonneg hs.1
        · linarith [hs.2, ht.length]
      have h₁ := hn.remaining_profile _ hzs
      have h₀ := hn.remaining_profile _ hz
      have htail := ht.profile s hs
      change f (tail.finalFamily.problem i) s - f (tail.finalFamily.problem i) 0 =
        f (source.problem i) (node.depth i + tail.totalDepth i + s) -
          f (source.problem i) (node.depth i + tail.totalDepth i)
      rw [show node.depth i + tail.totalDepth i + s =
        node.depth i + (tail.totalDepth i + s) by ring]
      linarith
    · change Horizon (source.problem i) ≤ node.cost i + tail.totalCost i +
        Horizon (tail.finalFamily.problem i)
      linarith [hn.composition, ht.horizon]

/-- Complete the last segment by actual true costs approaching its
horizon. The total cost then approaches the full critical horizon. -/
theorem terminal_completion (hinit : Initial)
    (path : GridPath ctx source start targets) (baseLength : ℝ)
    (hbase : source.length = (1 - start) * baseLength) :
    ∃ terminalCost : ℕ → ℝ,
      (∀ᶠ i in atTop, Cost (path.finalFamily.problem i) (terminalCost i)) ∧
      Tendsto (fun i => path.totalCost i + terminalCost i) atTop (𝓝 (ctx.κ * source.length)) ∧
      (∀ᶠ i in atTop,
        Horizon (source.problem i) ≤ path.totalCost i + terminalCost i) := by
  obtain ⟨terminalCost, hcost, hlim⟩ := exists_costs_tendsto hinit path.finalFamily.problem
    (ctx.κ * path.finalFamily.length)
    (Eventually.of_forall fun i => (path.finalFamily.angular i).1)
    path.finalFamily.horizon_limit
  refine ⟨terminalCost, hcost, ?_, ?_⟩
  · have ht := (path.totalCost_limit baseLength hbase).add hlim
    rw [path.final_length baseLength hbase] at ht
    convert ht using 2
    rw [hbase]
    ring
  · filter_upwards [path.path_law, hcost] with i hi hc
    have hH : Horizon (path.finalFamily.problem i) ≤ terminalCost i :=
      csInf_le ⟨0, fun _ hh => hh.1⟩ hc
    linarith [hi.horizon]

end GridPath

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
