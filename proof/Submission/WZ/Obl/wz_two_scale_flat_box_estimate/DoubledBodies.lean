-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.DoubledBodies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.TubeGeometry
import Submission.WZ.Obl.wz_flat_factored_improvement.ShortMap
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.AxisGeometry

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (tube_convex)

lemma tube_midpoint_mem {ρ : ℝ} (hρ : 0 < ρ) (y w : Space) :
    y + (1 / 2 : ℝ) • w ∈ Tube ρ y w := by
  apply self_subset_thickening hρ
  have hh := midpoint_mem_segment (𝕜 := ℝ) y (y + w)
  convert hh using 1
  rw [midpoint_eq_smul_add, invOf_eq_inv]
  module

lemma convex_subset_dilation_two {S : Set Space} (hS : Convex ℝ S) {q : Space}
    (hq : q ∈ S) : S ⊆ dilation q 2 (by norm_num) '' S := by
  intro p hp
  refine ⟨(1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q,
    hS hp hq (by norm_num) (by norm_num) (by norm_num), ?_⟩
  rw [dilation_apply]
  module

lemma tube_subset_doubled {ρ : ℝ} (hρ : 0 < ρ) (y w : Space) :
    Tube ρ y w ⊆ Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w) := by
  rw [doubled_tube_image]
  exact convex_subset_dilation_two (tube_convex _ _ _) (tube_midpoint_mem hρ y w)

lemma doubled_closed_subset_triple_box {ρ a b c : ℝ} (hρ : 0 < ρ)
    (y w z : Space) (e : Space ≃ₗᵢ[ℝ] Space)
    (hT : Tube ρ y w ⊆ Box a b c z e) :
    closure (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w)) ⊆
      Box (3 * a) (3 * b) (3 * c) z e := by
  apply closure_minimal _ (box_isClosed _ _ _ _ _)
  rw [doubled_tube_image]
  have hh := (image_mono (f := AffineMap.homothety (y + (1 / 2 : ℝ) • w) (2 : ℝ)) hT).trans
    (homothety_box_subset_triple (hT (tube_midpoint_mem hρ y w)))
  exact hh

lemma doubled_closed_compact (ρ : ℝ) (y w : Space) :
    IsCompact (closure (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w))) :=
  WangZahlLot.Obl.wz_flat_factored_improvement.closedTube_isCompact _ _ _

lemma doubled_closed_convex (ρ : ℝ) (y w : Space) :
    Convex ℝ (closure (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w))) :=
  (tube_convex _ _ _).closure

lemma doubled_closed_unit_bound {ρ : ℝ} (hρhalf : ρ ≤ 1 / 2)
    (y w : Space) (hw : ‖w‖ = 1)
    (hmeet : (Tube ρ y w ∩ ball (0 : Space) 1).Nonempty) :
    closure (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w)) ⊆
      closedBall (0 : Space) 4 := by
  obtain ⟨p, hp, hpB⟩ := hmeet
  have hpdist := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.tube_dist_midpoint hw hp
  have hmid : ‖y + (1 / 2 : ℝ) • w‖ < ρ + 3 / 2 := by
    have hh := dist_triangle (y + (1 / 2 : ℝ) • w) p 0
    rw [dist_comm _ p, dist_zero_right, dist_zero_right] at hh
    have hn := mem_ball_zero_iff.mp hpB
    linarith
  apply closure_minimal _ isClosed_closedBall
  rw [doubled_tube_image]
  rintro _ ⟨q, hq, rfl⟩
  have hqdist := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.tube_dist_midpoint hw hq
  rw [dist_eq_norm] at hqdist
  apply mem_closedBall_zero_iff.mpr
  rw [dilation_apply]
  have hh := norm_add_le ((2 : ℝ) • (q - (y + (1 / 2 : ℝ) • w))) (y + (1 / 2 : ℝ) • w)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  linarith

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
