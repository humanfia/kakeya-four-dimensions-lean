import Submission.Obl.k4_scalar_guarded_entropic_path.StageLayout
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewGrid

/-! The whole finite grid is chosen inside one quarter of the limiting
unit interval. Every possible original window then has length above one half. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

open Filter Set PathMeasures TrueLiftChains
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem GridPath.endpoint_lt_bound {ctx : CriticalContext} {source : MaximizingFamily ctx}
    {start : ℝ} {targets : List ℝ} (path : GridPath ctx source start targets)
    (b : ℝ) (hstart : start < b) (htargets : ∀ r ∈ targets, r < b) : path.endpoint < b := by
  induction path with
  | nil => exact hstart
  | cons r rs hs hr node tail ih =>
    exact ih (htargets r (List.mem_cons_self)) (fun s hs => htargets s (List.mem_cons_of_mem _ hs))

namespace TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}

theorem eventually_layout_final_length {k : ℕ} {R δ : ℝ}
    (q : StageLayout k R δ ctx.κ ctx.η) (path : TrueGridPath ctx source 0 q.targets)
    (hsource : source.length = 1) :
    ∀ᶠ i in atTop, (1 / 2 : ℝ) < L (path.forget.finalFamily.problem i) := by
  have hend : path.forget.endpoint < (1 / 4 : ℝ) :=
    path.forget.endpoint_lt_bound _ (by norm_num) q.targets_small
  have hlength : (1 / 2 : ℝ) < path.forget.finalFamily.length := by
    rw [path.forget.final_length 1 (by simpa only [sub_zero, one_mul] using hsource)]
    linarith
  exact path.forget.finalFamily.length_limit.eventually (lt_mem_nhds hlength)

theorem viewAt_positive_prefix {start : ℝ} {targets : List ℝ} {root : Code}
    (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) {n : ℕ} (hn : 0 < n)
    (hlen : 0 < targets.length) : 0 < (path.viewAt i certs hl before n).prefixChain.length := by
  rw [path.viewAt_prefix_length]
  have hm : 0 < min n targets.length := lt_min hn hlen
  omega

/-- All actual stage views are formed with the literal empty original
prefix. The zero view is used for master velocity widths; candidates
begin at its positive successors. -/
def stageViews {start : ℝ} {targets : List ℝ}
    (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i) :
    Fin (targets.length + 1) →
      OriginalView (source.problem i) (path.forget.finalFamily.problem i) (ctx.D i) ctx.S₀ ctx.η :=
  fun n => path.viewAt i certs hl (.nil _ (source.angular i).1) n.val

theorem stageViews_referenceFactor_le {start : ℝ} {targets : List ℝ}
    (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (a : Fin (targets.length + 1)) (k : ℕ) :
    (path.stageViews i certs hl a).suffixChain.referenceFactor k ≤
      (path.measuredChain i certs).referenceFactor k :=
  path.viewAt_referenceFactor_le i certs hl _ a.val k

end TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
