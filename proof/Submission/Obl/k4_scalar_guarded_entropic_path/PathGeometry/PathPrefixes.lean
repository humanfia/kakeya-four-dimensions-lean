/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/PathPrefixes.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FinitePaths

/-!
All finite prefixes retain the same critical path and original exponent
units. Each prefix inherits the actual layer witnesses and rate limits.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.GridPath

open Set Filter
open scoped Topology

/-- The first `n` nodes, with the same actual splits as the full path. -/
def take {ctx : CriticalContext} {source : MaximizingFamily ctx} {start : ℝ}
    {targets : List ℝ} (path : GridPath ctx source start targets) (n : ℕ) :
    GridPath ctx source start (targets.take n) :=
  match n with
  | 0 => .nil source start
  | n + 1 =>
      match path with
      | .nil source start => .nil source start
      | .cons r rs hstart hr node tail =>
          .cons r (rs.take n) hstart hr node (tail.take n)

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- Each prefix ends at the corresponding prescribed target. -/
theorem endpoint_take_succ (path : GridPath ctx source start targets)
    (n : ℕ) (hn : n < targets.length) :
    (path.take (n + 1)).endpoint = targets[n] := by
  induction path generalizing n with
  | nil => simp at hn
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero => simp [take, endpoint]
    | succ n => exact ih n (Nat.lt_of_succ_lt_succ hn)

/-- Prefix depths converge to their own targets in the original units. -/
theorem prefix_depth_limit (path : GridPath ctx source start targets)
    (baseLength : ℝ) (hbase : source.length = (1 - start) * baseLength)
    (n : ℕ) (hn : n < targets.length) :
    Tendsto (path.take (n + 1)).totalDepth atTop
      (𝓝 ((targets[n] - start) * baseLength)) := by
  simpa only [path.endpoint_take_succ n hn] using
    (path.take (n + 1)).totalDepth_limit baseLength hbase

/-- Prefix costs converge to the same critical rate times actual depth. -/
theorem prefix_cost_limit (path : GridPath ctx source start targets)
    (baseLength : ℝ) (hbase : source.length = (1 - start) * baseLength)
    (n : ℕ) (hn : n < targets.length) :
    Tendsto (path.take (n + 1)).totalCost atTop
      (𝓝 (ctx.κ * ((targets[n] - start) * baseLength))) := by
  simpa only [path.endpoint_take_succ n hn] using
    (path.take (n + 1)).totalCost_limit baseLength hbase

/-- Every prefix profile law and horizon composition bound holds on one
common outer tail. This is a finite intersection, not an inner diagonal. -/
theorem eventually_all_prefix_laws (path : GridPath ctx source start targets) :
    ∀ᶠ i in atTop, ∀ n : Fin (targets.length + 1),
      PathLaw (source.problem i) ((path.take n).finalFamily.problem i)
        ((path.take n).totalDepth i) ((path.take n).totalCost i) := by
  apply Filter.eventually_all.2
  intro n
  exact (path.take n).path_law

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.GridPath
