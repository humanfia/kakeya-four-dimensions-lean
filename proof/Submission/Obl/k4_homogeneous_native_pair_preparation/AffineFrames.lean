-- Adapted from this LOT tree, o206, session x0709, commit f7d6ac58,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/SpineFrames.lean.
import Submission.Obl.k4_homogeneous_native_pair_preparation.Model

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.Construction

open Matrix

noncomputable def frameOffset (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)

theorem y_eq_add_smul (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : y l t = y l 0 + t • v l := by
  ext i
  fin_cases i <;> simp [y, v, x]

/-- The frame offset is affine in time. -/
theorem frameOffset_sub (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t t' : ℝ) :
    frameOffset c u Q l t - frameOffset c u Q l t' =
      (t - t') • Matrix.toEuclideanLin Q⁻¹ (v l - u) := by
  unfold frameOffset
  rw [← map_sub, ← map_smul]
  congr 1
  rw [y_eq_add_smul l t, y_eq_add_smul l t']
  module

theorem norm_sq_two (w : EuclideanSpace ℝ (Fin 2)) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs]

end Submission.Obl.k4_homogeneous_native_pair_preparation.Construction
