import Submission.Obl.k4_scalar_guarded_entropic_path.Info.PointGridGaps
import Submission.Obl.k4_scalar_guarded_entropic_path.StageLayout

/-! The exact stage layout gives the strict two-scale point-state
margins in every candidate original frame. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open PathGeometry PathGeometry.PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {stage : ℕ} {R δ κ η rootD rootS rootη : ℝ} {root final : Code}

def layoutPointCoarse (q : StageLayout stage R δ κ η) {count : ℕ} (hc : q.C ≤ count) : Fin count :=
  ⟨q.coarse, by have := q.coarse_lt; omega⟩

def layoutPointFine (q : StageLayout stage R δ κ η) {count : ℕ} (hc : q.C ≤ count) : Fin count :=
  ⟨q.C - 1, by have := q.coarse_lt; omega⟩

theorem layoutPoint_ordered (q : StageLayout stage R δ κ η) {count : ℕ} (hc : q.C ≤ count) :
    layoutPointCoarse q hc ≤ layoutPointFine q hc := by
  change q.coarse ≤ q.C - 1
  have := q.coarse_lt
  omega

theorem layoutPoint_future (q : StageLayout stage R δ κ η) {count : ℕ} (hc : q.C ≤ count) :
    (layoutPointFine q hc).val + 1 = q.C := by
  change q.C - 1 + 1 = q.C
  have := q.coarse_lt
  omega

theorem layout_point_depth_gaps (q : StageLayout stage R δ κ η)
    (a : OriginalView root final rootD rootS rootη) (hc : q.C ≤ a.count)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) {error v : ℝ}
    (herror : 0 ≤ error) (herrorSmall : error ≤ q.scale / 8) (hv : v ≤ q.scale / 8)
    (hgrid : PathNodes.TrueGridPath.GridControl a κ (q.scale * q.mesh) 1 error) :
    q.scale * ((q.m : ℝ) + 1) ≤ a.depth (layoutPointCoarse q hc) ∧
      q.scale * ((q.m : ℝ) + 1) ≤
        κ * (a.depth (layoutPointFine q hc) - a.depth (layoutPointCoarse q hc)) - 2 * v := by
  let c := layoutPointCoarse q hc
  let f := layoutPointFine q hc
  have hcoarse := (hgrid c).1
  have hfine := (hgrid f).1
  have hC : (f.val : ℝ) + 1 = (q.C : ℝ) := by
    exact_mod_cast layoutPoint_future q hc
  change |a.depth c - (((q.coarse : ℝ) + 1) * (q.scale * q.mesh) * 1)| ≤ error at hcoarse
  rw [hC, mul_one] at hfine
  rw [mul_one] at hcoarse
  have hci : q.scale * ((q.m : ℝ) + 2) ≤ ((q.coarse : ℝ) + 1) * (q.scale * q.mesh) := by
    have h := mul_le_mul_of_nonneg_left q.coarse_depth q.scale_pos.le
    nlinarith only [h]
  have hgi : q.scale * ((q.m : ℝ) + 2) ≤ κ *
      ((q.C : ℝ) * (q.scale * q.mesh) - ((q.coarse : ℝ) + 1) * (q.scale * q.mesh)) := by
    have h := mul_le_mul_of_nonneg_left q.depth_gap q.scale_pos.le
    nlinarith only [h]
  exact point_depth_gaps_of_margins hκ hκ1 herror (by linarith [q.scale_pos])
    (by linarith [q.scale_pos]) hci hgi hcoarse hfine

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
