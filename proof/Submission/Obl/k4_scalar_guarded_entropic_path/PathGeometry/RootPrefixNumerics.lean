/-
Adapted from this LOT tree, obligation o093, session x0535, commit 62576536,
Submission/Obl/k4_scalar_critical_path_terminal/RootPrefixNumerics.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPrefixCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPrefixes

/-! The root charts use the SAME actual cumulative prefix depths and
critical time costs as the original numerical GridPath. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open Set Filter
open scoped Topology

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

theorem prefixDepth_eq_take (path : TrueGridPath ctx source start targets)
    (i : ℕ) (j : Fin targets.length) :
    path.prefixDepth i j = (path.forget.take (j.val + 1)).totalDepth i := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · cases tail <;> simp [prefixDepth, forget, GridPath.take, GridPath.totalDepth]
    · change node.depth i + tail.prefixDepth i j =
        node.depth i + (tail.forget.take (j.val + 1)).totalDepth i
      rw [ih j]

theorem prefixCost_eq_take (path : TrueGridPath ctx source start targets)
    (i : ℕ) (j : Fin targets.length) :
    path.prefixCost i j = (path.forget.take (j.val + 1)).totalCost i := by
  induction path with
  | nil => exact Fin.elim0 j
  | cons r rs hstart hr node tail ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · cases tail <;> simp [prefixCost, forget, GridPath.take, GridPath.totalCost]
    · change node.cost i + tail.prefixCost i j =
        node.cost i + (tail.forget.take (j.val + 1)).totalCost i
      rw [ih j]

theorem root_prefix_depth_limit (path : TrueGridPath ctx source start targets)
    (baseLength : ℝ) (hbase : source.length = (1 - start) * baseLength)
    (j : Fin targets.length) :
    Tendsto (fun i => path.prefixDepth i j) atTop
      (nhds ((targets[j.val] - start) * baseLength)) := by
  have heq : (fun i => path.prefixDepth i j) = (path.forget.take (j.val + 1)).totalDepth :=
    funext fun i => path.prefixDepth_eq_take i j
  rw [heq]
  exact path.forget.prefix_depth_limit baseLength hbase j.val j.isLt

theorem root_prefix_cost_limit (path : TrueGridPath ctx source start targets)
    (baseLength : ℝ) (hbase : source.length = (1 - start) * baseLength)
    (j : Fin targets.length) :
    Tendsto (fun i => path.prefixCost i j) atTop
      (nhds (ctx.κ * ((targets[j.val] - start) * baseLength))) := by
  have heq : (fun i => path.prefixCost i j) = (path.forget.take (j.val + 1)).totalCost :=
    funext fun i => path.prefixCost_eq_take i j
  rw [heq]
  exact path.forget.prefix_cost_limit baseLength hbase j.val j.isLt

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
