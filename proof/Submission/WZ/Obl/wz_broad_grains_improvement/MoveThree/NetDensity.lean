-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NetDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NetDensity.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 7652d3d, NetDensity.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BalancedNet
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.TubeBodies
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Tubes

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube closedTube_volume_bounds tube_subset_closedTube)

/-- The net carriers have room to close while staying in the open unit ball. -/
theorem closed_net_carrier_subset_ball {b : ℝ} (hb : 0 < b)
    (hbsmall : b ≤ 1 / 1000000) {c : V} {u : Fin 3 → V}
    (hu : Orthonormal ℝ u) (hc : ‖c‖ < 1 / 100) :
    closedTube (4 * b) (c - (1 / 2 : ℝ) • axisDir u) (axisDir u) ⊆ ball (0 : V) 1 := by
  apply subset_trans (b := T (8 * b) (c - (1 / 2 : ℝ) • axisDir u) (axisDir u))
  · exact (closure_thickening_subset_cthickening _ _).trans
      (cthickening_subset_thickening' (by positivity) (by linarith) _)
  · exact WangZahlLot.Obl.wz_affine_robust_cluster_estimate.centered_tube_subset_ball
      (norm_axisDir hu) (by linarith) (by linarith)

/-- The dense representative supplies density to its carrier, regardless of which
of the other covered prisms survive equal-fibre selection. -/
theorem net_carrier_density {a b D : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 0 < b) (hbsmall : b ≤ 1 / 1000000) (hD : 0 ≤ D)
    {c : V} {u : Fin 3 → V} (hu : Orthonormal ℝ u) {Y Γ : Set V}
    (hY : Y ⊆ Γ ∩ prism a b c u) (hden : O (D * b ^ 2) ≤ μ Y) :
    O (D / 6144) * μ (closedTube (4 * b) (c - (1 / 2 : ℝ) • axisDir u) (axisDir u)) ≤
      μ (closedTube (4 * b) (c - (1 / 2 : ℝ) • axisDir u) (axisDir u) ∩ Γ) := by
  have hvol := (closedTube_volume_bounds (by positivity : 0 < 4 * b)
    (by linarith : 4 * b ≤ 1) (c - (1 / 2 : ℝ) • axisDir u)
    (axisDir u) (norm_axisDir hu)).2
  have hsub : Y ⊆ closedTube (4 * b) (c - (1 / 2 : ℝ) • axisDir u) (axisDir u) ∩ Γ := by
    intro p hp
    exact ⟨tube_subset_closedTube _ _ _ (prism_subset_cTube ha hab hb hu (hY hp).2),
      (hY hp).1⟩
  calc
    _ ≤ O (D / 6144) * O (384 * (4 * b) ^ 2) := mul_le_mul' le_rfl hvol
    _ = O (D * b ^ 2) := by
      dsimp only [O]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ μ Y := hden
    _ ≤ _ := measure_mono hsub

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
