import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewAt
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ParentNumerics
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPrefixNumerics

/-! Arithmetic prescribed targets give a uniform relative grid inside
EVERY actual window parent, before selecting its inner sample or law. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open Filter Set
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open TrueLiftChains PathMeasures

noncomputable section

namespace PathNodes.TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

/-- All current-parent actual root depths and time costs approach the
same relative uniform grid. -/
theorem eventually_root_grid_bounds (path : TrueGridPath ctx source start targets)
    (baseLength Δ ε : ℝ) (hbase : source.length = (1 - start) * baseLength)
    (hgrid : ∀ j : Fin targets.length, targets[j.val] = start + ((j.val : ℝ) + 1) * Δ)
    (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ j : Fin targets.length,
      |path.prefixDepth i j - (((j.val : ℝ) + 1) * Δ * baseLength)| ≤ ε ∧
      |path.prefixCost i j - ctx.κ * path.prefixDepth i j| ≤ ε := by
  apply Filter.eventually_all.2
  intro j
  have hd := path.root_prefix_depth_limit baseLength hbase j
  have ht := path.root_prefix_cost_limit baseLength hbase j
  have htarget : (targets[j.val] - start) * baseLength =
      ((j.val : ℝ) + 1) * Δ * baseLength := by rw [hgrid j]; ring
  have hdepth : Tendsto (fun i => |path.prefixDepth i j -
      (((j.val : ℝ) + 1) * Δ * baseLength)|) atTop (nhds 0) := by
    rw [← htarget]
    simpa only [sub_self, abs_zero] using
      (hd.sub (tendsto_const_nhds (x := (targets[j.val] - start) * baseLength))).abs
  have htime : Tendsto (fun i => |path.prefixCost i j - ctx.κ * path.prefixDepth i j|)
      atTop (nhds 0) := by
    simpa only [sub_self, abs_zero] using (ht.sub (hd.const_mul ctx.κ)).abs
  exact (hdepth.eventually (ge_mem_nhds hε)).and (htime.eventually (ge_mem_nhds hε))

/-- The control is expressed in the actual normalized parent's original
units. Subtracting global node depths introduces no change of scale. -/
def GridControl {root final : Code} {D S₀ η : ℝ}
    (a : OriginalView root final D S₀ η) (κ Δ baseLength ε : ℝ) : Prop :=
  ∀ j : Fin a.count,
    |a.depth j - (((j.val : ℝ) + 1) * Δ * baseLength)| ≤ ε ∧
    |a.time j - κ * a.depth j| ≤ ε

/-- All potential original parents satisfy the SAME relative-grid
bounds on one outer tail, even though their exact samples differ. -/
theorem eventually_viewAt_gridControl (path : TrueGridPath ctx source start targets)
    (baseLength Δ ε : ℝ) (hbase : source.length = (1 - start) * baseLength)
    (hgrid : ∀ j : Fin targets.length, targets[j.val] = start + ((j.val : ℝ) + 1) * Δ)
    (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ (certs : path.Certificates i) (hl : path.forget.AllLayers i)
      (root : Code) (before : Chain root (source.problem i)) (n : ℕ),
      GridControl (path.viewAt i certs hl before n) ctx.κ Δ baseLength ε := by
  induction path with
  | nil =>
    exact Eventually.of_forall fun i certs hl root before n j => Fin.elim0 j
  | @cons source start r rs hstart hr node tail ih =>
    have hden : 1 - start ≠ 0 := (sub_pos.mpr (hstart.trans hr)).ne'
    have hnext : node.remaining.length = (1 - r) * baseLength := by
      rw [node.remaining_length, hbase]
      field_simp [hden]
      ring
    have hfirst : r = start + Δ := by
      simpa only [List.getElem_cons_zero, Fin.val_zero, Nat.cast_zero, zero_add, one_mul]
        using hgrid ⟨0, by simp⟩
    have htailgrid : ∀ j : Fin rs.length, rs[j.val] = r + ((j.val : ℝ) + 1) * Δ := by
      intro j
      calc
        rs[j.val] = start + ((j.val : ℝ) + 1 + 1) * Δ := by
          simpa only [List.getElem_cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one]
            using hgrid j.succ
        _ = r + ((j.val : ℝ) + 1) * Δ := by rw [hfirst]; ring
    filter_upwards [(TrueGridPath.cons r rs hstart hr node tail).eventually_root_grid_bounds
      baseLength Δ ε hbase hgrid hε, ih hnext htailgrid] with i hhead htail
    intro certs hl root before n
    cases n with
    | zero => exact hhead
    | succ n => exact htail certs.2 hl.2 root _ n

/-- The uniform original profile and known-cost controls also hold in
every numbered parent, before choosing the information window. -/
theorem eventually_viewAt_parentControl (path : TrueGridPath ctx source start targets)
    (hcalc : Calculus) (ε gain : ℝ) (hε : 0 < ε) (hgain : 0 < gain) :
    ∀ᶠ i in atTop, ∀ (certs : path.Certificates i) (hl : path.forget.AllLayers i)
      (root : Code) (before : Chain root (source.problem i)) (n : ℕ),
      ParentControl ctx ε gain (path.viewAt i certs hl before n).parent := by
  filter_upwards [path.eventually_originalViews_parentControl hcalc ε gain hε hgain] with i hi
  intro certs hl root before n
  exact hi certs hl root before _ (path.viewAt_mem_originalViews i certs hl before n)

end PathNodes.TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
