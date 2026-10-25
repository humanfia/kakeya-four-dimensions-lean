-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.HessianCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/HessianCoordinates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/HessianCoordinates.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/HessianCoordinates.lean. Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/HessianCoordinates.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.GradientFreeze

/-! # Actual Hessian bounds from the coordinate-gradient derivatives -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set Metric

noncomputable section

def gradientComponent (g : EuclideanSpace ℝ (Fin 3) → ℝ) (j : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ := derivativeCoordinate (fderiv ℝ g x) j

/-- Evaluating the derivative on a fixed coordinate vector commutes with
actual Frechet differentiation. -/
theorem fderiv_gradientComponent
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3))
    (hdf : DifferentiableAt ℝ (fderiv ℝ g) x) (j : Fin 3) :
    fderiv ℝ (gradientComponent g j) x =
      (fderiv ℝ (fderiv ℝ g) x).flip (spacetimeBasis j) := by
  unfold gradientComponent derivativeCoordinate
  rw [fderiv_clm_apply hdf (differentiableAt_const (spacetimeBasis j))]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]

/-- Three coordinate bounds control the operator norm of the SAME
continuous linear functional. -/
theorem derivative_norm_le_three_coordinates
    (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ j, |derivativeCoordinate F j| ≤ C) : ‖F‖ ≤ 3 * C := by
  apply F.opNorm_le_bound (by positivity)
  intro y
  rw [Real.norm_eq_abs, derivative_apply_eq_sum]
  calc
    _ ≤ ∑ j, |derivativeCoordinate F j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, C * ‖y‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hcoord j) (PiLp.norm_apply_le y j) (abs_nonneg _) hC
    _ = (3 * C) * ‖y‖ := by simp; ring

/-- Coordinate-gradient jet norming controls the ACTUAL second jet,
without an independently supplied Hessian witness. -/
theorem hessian_norm_le_coordinate_gradients
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3))
    (hdf : DifferentiableAt ℝ (fderiv ℝ g) x) {C : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ j, ‖fderiv ℝ (gradientComponent g j) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ 2 g x‖ ≤ 3 * C := by
  rw [← norm_second_derivative]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have hy : ‖fderiv ℝ (fderiv ℝ g) x y‖ ≤ 3 * (C * ‖y‖) := by
    apply derivative_norm_le_three_coordinates _ (by positivity)
    intro j
    calc
      |derivativeCoordinate (fderiv ℝ (fderiv ℝ g) x y) j| =
          ‖fderiv ℝ (gradientComponent g j) x y‖ := by
        rw [fderiv_gradientComponent g x hdf, Real.norm_eq_abs]
        rfl
      _ ≤ ‖fderiv ℝ (gradientComponent g j) x‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖y‖ := mul_le_mul_of_nonneg_right (hcoord j) (norm_nonneg _)
  simpa only [mul_assoc] using hy

/-- The original smooth residual has an actual maximum gradient norm on
the comparison core. This provides the quantity absorbed by renewal. -/
theorem exists_core_gradient_max
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : ContDiffOn ℝ 2 g (ball 0 4)) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2, ‖fderiv ℝ g x‖ ≤ M) ∧
      ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2, M = ‖fderiv ℝ g x‖ := by
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ g) (ball 0 4) :=
    hg.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hsub : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 ⊆ ball 0 4 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_ball, dist_zero_right]
    linarith
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2).exists_isMaxOn
    (show (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2).Nonempty from ⟨0, by simp⟩)
    (hdf.continuousOn.norm.mono hsub)
  exact ⟨‖fderiv ℝ g x‖, norm_nonneg _, (isMaxOn_iff.mp hmax), x, hx, rfl⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
