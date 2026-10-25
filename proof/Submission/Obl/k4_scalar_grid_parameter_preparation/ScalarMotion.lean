/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/ScalarMotion.lean -/
import Mathlib

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

/-- The concrete scalar tangent trajectories have uniform motion on bounded
time intervals, with their original coefficient bound. -/
theorem scalar_quadratic_motion_le (a : Fin 5 → ℝ) (H t u : ℝ) (_hH : 0 ≤ H)
    (ha : ∀ e, |a e| ≤ H) (ht : |t| ≤ 2) (hu : |u| ≤ 2) :
    dist (a 0 + u * a 1) (a 0 + t * a 1) ≤ H * dist u t ∧
      dist (a 2 + u * a 3 + u ^ 2 * a 4) (a 2 + t * a 3 + t ^ 2 * a 4) ≤
        5 * H * dist u t := by
  have hy : a 0 + u * a 1 - (a 0 + t * a 1) = (u - t) * a 1 := by ring
  have hx : a 2 + u * a 3 + u ^ 2 * a 4 - (a 2 + t * a 3 + t ^ 2 * a 4) =
      (u - t) * (a 3 + (u + t) * a 4) := by ring
  have hsum : |u + t| ≤ 4 := (abs_add_le _ _).trans (by linarith)
  have hb : |a 3 + (u + t) * a 4| ≤ 5 * H := by
    calc
      _ ≤ |a 3| + |u + t| * |a 4| := by simpa only [abs_mul] using abs_add_le (a 3) ((u + t) * a 4)
      _ ≤ H + 4 * H := add_le_add (ha 3)
        (mul_le_mul hsum (ha 4) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  simp only [Real.dist_eq]
  constructor
  · rw [hy, abs_mul]
    exact (mul_le_mul_of_nonneg_left (ha 1) (abs_nonneg _)).trans_eq (mul_comm _ _)
  · rw [hx, abs_mul]
    exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_comm _ _)

end Submission.Obl.k4_scalar_grid_parameter_preparation
