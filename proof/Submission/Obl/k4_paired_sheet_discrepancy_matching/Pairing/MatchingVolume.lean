/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/MatchingVolume.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SheetBridge

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set Metric

noncomputable def matchingVolumeConstant : ℝ :=
  (volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2))).toReal + 1

theorem matchingVolumeConstant_pos : 0 < matchingVolumeConstant := by
  unfold matchingVolumeConstant
  positivity

theorem matching_grid_ball_volume {r : ℝ} (hr : 0 < r) (c : EuclideanSpace ℝ (Fin 3)) :
    volume (closedBall c (r / 2)) ≤ ENNReal.ofReal (matchingVolumeConstant * (2 * r) ^ 3) := by
  have hpre : {z : EuclideanSpace ℝ (Fin 3) |
      (2 * r)⁻¹ • (z - c) ∈ closedBall 0 (1 / 2)} = closedBall c r := by
    ext z
    simp only [mem_setOf_eq, mem_closedBall_zero_iff, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * r)⁻¹), mem_closedBall_iff_norm]
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * r)]
    congr 1
    ring
  have hv := volume_affine_preimage c (by positivity : (0 : ℝ) < 2 * r)
    (closedBall 0 (1 / 2))
  rw [hpre] at hv
  have hfin : volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≠ ⊤ :=
    (isCompact_closedBall _ _).measure_ne_top
  calc
    _ ≤ volume (closedBall c r) := measure_mono (closedBall_subset_closedBall (by linarith))
    _ = ENNReal.ofReal ((2 * r) ^ 3) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) := hv
    _ ≤ ENNReal.ofReal ((2 * r) ^ 3) * ENNReal.ofReal matchingVolumeConstant := by
      apply mul_le_mul' le_rfl
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal (by dsimp [matchingVolumeConstant]; linarith)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * r) ^ 3)]
      congr 1
      ring

theorem matching_grid_weight {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ((gridBox (r / 2) (1 / 8)).card : ℝ) * (2 * r) ^ 3 ≤ 1331 := by
  have hc := card_gridBox (r / 2) (1 / 8) (by norm_num) (by positivity)
  calc _ ≤ (2 * (1 / 8) / (r / 2) + 5) ^ 3 * (2 * r) ^ 3 :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = ((2 * (1 / 8) / (r / 2) + 5) * (2 * r)) ^ 3 := (mul_pow _ _ _).symm
    _ = (1 + 10 * r) ^ 3 := by congr 1; field_simp; ring
    _ ≤ (11 : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    _ = 1331 := by norm_num

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
