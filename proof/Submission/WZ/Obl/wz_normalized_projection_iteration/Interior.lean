-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Interior.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Basic

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric

/-- Move a segment's midpoint inward while keeping its length and direction. -/
noncomputable def inwardStart (r : ℝ) (x v : Space) : Space :=
  x - (4 * r) • (x + (1 / 2 : ℝ) • v)

theorem inward_start_norm {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4)
    {x v : Space} (hx : ‖x‖ ≤ 1) (hv : ‖v‖ = 1) :
    ‖inwardStart r x v‖ ≤ 1 - 2 * r := by
  have heq : inwardStart r x v = (1 - 4 * r) • x - (2 * r) • v := by
    unfold inwardStart
    module
  rw [heq]
  calc
    ‖(1 - 4 * r) • x - (2 * r) • v‖ ≤
        ‖(1 - 4 * r) • x‖ + ‖(2 * r) • v‖ := norm_sub_le _ _
    _ = (1 - 4 * r) * ‖x‖ + 2 * r := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ 1 - 4 * r), abs_of_nonneg (by positivity), hv, mul_one]
    _ ≤ 1 - 2 * r := by nlinarith

theorem inward_end_norm {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4)
    {x v : Space} (hx : ‖x + v‖ ≤ 1) (hv : ‖v‖ = 1) :
    ‖inwardStart r x v + v‖ ≤ 1 - 2 * r := by
  have heq : inwardStart r x v + v = inwardStart r (x + v) (-v) := by
    unfold inwardStart
    module
  rw [heq]
  exact inward_start_norm hr hr1 hx (by simpa using hv)

theorem inward_tube_subset_ball {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 4)
    {x v : Space} (hx : ‖x‖ ≤ 1) (hxv : ‖x + v‖ ≤ 1) (hv : ‖v‖ = 1) :
    Tube r (inwardStart r x v) v ⊆ ball 0 1 := by
  have hseg : segment ℝ (inwardStart r x v) (inwardStart r x v + v) ⊆
      closedBall (0 : Space) (1 - 2 * r) :=
    (convex_closedBall (0 : Space) (1 - 2 * r)).segment_subset
      (by simpa using inward_start_norm hr.le hr1 hx hv)
      (by simpa using inward_end_norm hr.le hr1 hxv hv)
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
  have hznorm : ‖z‖ ≤ 1 - 2 * r := by simpa using hseg hz
  rw [mem_ball, dist_zero_right]
  have htriangle := norm_le_norm_add_norm_sub z p
  rw [← dist_eq_norm, dist_comm z p] at htriangle
  linarith

theorem inward_start_dist {r : ℝ} (hr : 0 ≤ r) {x v : Space}
    (hx : ‖x‖ ≤ 1) (hv : ‖v‖ = 1) : dist (inwardStart r x v) x ≤ 6 * r := by
  have hmid : ‖x + (1 / 2 : ℝ) • v‖ ≤ 3 / 2 := by
    calc
      _ ≤ ‖x‖ + ‖(1 / 2 : ℝ) • v‖ := norm_add_le _ _
      _ ≤ 3 / 2 := by
        norm_num [norm_smul, hv]
        linarith
  rw [dist_eq_norm, inwardStart]
  have heq : x - (4 * r) • (x + (1 / 2 : ℝ) • v) - x =
      -((4 * r) • (x + (1 / 2 : ℝ) • v)) := by abel
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

end WangZahlLot.Obl.wz_normalized_projection_iteration
