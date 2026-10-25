-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.TubeBodies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

/-- Compact convex reference bodies for the original open tubes. -/
def closedTube (δ : ℝ) (x v : E) : Set E := closure (tube δ x v)

lemma tube_convex (δ : ℝ) (x v : E) : Convex ℝ (tube δ x v) :=
  (convex_segment (𝕜 := ℝ) x (x + v)).thickening δ

lemma closedTube_convex (δ : ℝ) (x v : E) : Convex ℝ (closedTube δ x v) :=
  (tube_convex δ x v).closure

lemma tube_subset_closedTube (δ : ℝ) (x v : E) : tube δ x v ⊆ closedTube δ x v := subset_closure

lemma ball_subset_tube {δ : ℝ} (x v : E) : Metric.ball x δ ⊆ tube δ x v := by
  intro p hp
  exact Metric.mem_thickening_iff.mpr ⟨x, left_mem_segment ℝ x (x + v), hp⟩

lemma closedTube_subset_closedBall {δ : ℝ} {x v : E}
    (hb : tube δ x v ⊆ Metric.ball (0 : E) 1) :
    closedTube δ x v ⊆ Metric.closedBall (0 : E) 1 :=
  closure_minimal (hb.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall

lemma closedTube_compact {δ : ℝ} {x v : E}
    (hb : tube δ x v ⊆ Metric.ball (0 : E) 1) : IsCompact (closedTube δ x v) :=
  (isCompact_closedBall (0 : E) 1).of_isClosed_subset isClosed_closure (closedTube_subset_closedBall hb)

lemma volume_closedTube (δ : ℝ) (x v : E) : volume (closedTube δ x v) = volume (tube δ x v) :=
  measure_closure_of_null_frontier ((tube_convex δ x v).addHaar_frontier volume)

lemma closedTube_volume_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x v : E) (hv : ‖v‖ = 1) :
    ENNReal.ofReal (δ ^ 2) ≤ volume (closedTube δ x v) ∧
      volume (closedTube δ x v) ≤ ENNReal.ofReal (384 * δ ^ 2) := by
  rw [volume_closedTube]
  exact ⟨WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hδ x v hv,
    WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le hδ hδ1 x v hv⟩

lemma closedTube_endpoints {δ : ℝ} (hδ : 0 < δ) (x v : E) :
    x ∈ closedTube δ x v ∧ x + v ∈ closedTube δ x v := by
  constructor
  · exact subset_closure (Metric.self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  · exact subset_closure (Metric.self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
