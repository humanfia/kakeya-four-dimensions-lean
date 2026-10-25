-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.Directions.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def capDirection (u : Plane) : LeanEval.Analysis.WangZahlKakeya.Space :=
  !₂[u 0, u 1, Real.sqrt (1 - ‖u‖ ^ 2)]

theorem norm_capDirection {u : Plane} (hu : ‖u‖ ≤ 1 / 4) : ‖capDirection u‖ = 1 := by
  have hsq : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hnonneg : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  have h : ‖capDirection u‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [capDirection, Fin.sum_univ_succ, Real.sq_sqrt hnonneg]
    nlinarith [hsq]
  nlinarith [norm_nonneg (capDirection u)]

theorem dist_le_dist_capDirection (u w : Plane) :
    dist u w ≤ dist (capDirection u) (capDirection w) := by
  have h1 : ‖u - w‖ ^ 2 = (u 0 - w 0) ^ 2 + (u 1 - w 1) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h2 : ‖capDirection u - capDirection w‖ ^ 2 =
      (u 0 - w 0) ^ 2 + (u 1 - w 1) ^ 2 +
        (Real.sqrt (1 - ‖u‖ ^ 2) - Real.sqrt (1 - ‖w‖ ^ 2)) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, capDirection, Fin.sum_univ_succ]
    ring
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith [norm_nonneg (u - w), norm_nonneg (capDirection u - capDirection w),
    sq_nonneg (Real.sqrt (1 - ‖u‖ ^ 2) - Real.sqrt (1 - ‖w‖ ^ 2))]

theorem capDirection_last_ge {u : Plane} (hu : ‖u‖ ≤ 1 / 4) :
    1 / 2 ≤ capDirection u 2 := by
  change 1 / 2 ≤ Real.sqrt (1 - ‖u‖ ^ 2)
  apply (Real.le_sqrt (by norm_num) (by nlinarith [norm_nonneg u])).mpr
  nlinarith [norm_nonneg u]

theorem one_le_norm_capDirection_add {u w : Plane}
    (hu : ‖u‖ ≤ 1 / 4) (hw : ‖w‖ ≤ 1 / 4) :
    1 ≤ ‖capDirection u + capDirection w‖ := by
  have h := PiLp.norm_apply_le (capDirection u + capDirection w) (2 : Fin 3)
  have hu' := capDirection_last_ge hu
  have hw' := capDirection_last_ge hw
  have habs := le_abs_self (capDirection u 2 + capDirection w 2)
  simp only [PiLp.add_apply, Real.norm_eq_abs] at h
  linarith

end WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate
