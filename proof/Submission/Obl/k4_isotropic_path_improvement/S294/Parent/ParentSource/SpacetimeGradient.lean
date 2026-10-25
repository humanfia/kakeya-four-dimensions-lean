-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SpacetimeGradient, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SpacetimeGradient.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SpacetimeGradient.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SpacetimeGradient.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o204, session x0747, commit7ddecf81.
-- Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/SpacetimeGradient.lean; existing source attributions retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.GradientBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames

/-! # Actual spacetime derivatives from original broad directional tests -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped BigOperators

noncomputable section

def spacetimeBasis (j : Fin 3) : EuclideanSpace ℝ (Fin 3) := PiLp.single 2 j 1

def derivativeCoordinate (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (j : Fin 3) : ℝ :=
  F (spacetimeBasis j)

def derivativeSpatialRow (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![derivativeCoordinate F 1, derivativeCoordinate F 2]

def spacetimeDirection (V : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![1, V 0, V 1]

theorem derivative_apply_eq_sum (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    F x = ∑ j, derivativeCoordinate F j * x j := by
  have hx : x = ∑ j, x j • spacetimeBasis j := by
    ext i
    simp [spacetimeBasis, Pi.single_apply]
  calc
    _ = F (∑ j, x j • spacetimeBasis j) := congrArg F hx
    _ = ∑ j, derivativeCoordinate F j * x j := by
      simp [derivativeCoordinate, map_sum, mul_comm]

theorem derivative_spacetime_direction (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (V : EuclideanSpace ℝ (Fin 2)) :
    F (spacetimeDirection V) = derivativeCoordinate F 0 + inner ℝ V (derivativeSpatialRow F) := by
  rw [derivative_apply_eq_sum]
  simp [spacetimeDirection, derivativeSpatialRow, Fin.sum_univ_three, Fin.sum_univ_two,
    PiLp.inner_apply, mul_comm, add_assoc]

theorem derivative_coordinate_distance
    (F G : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (j : Fin 3) :
    |derivativeCoordinate F j - derivativeCoordinate G j| ≤ ‖F - G‖ := by
  calc
    _ = ‖(F - G) (spacetimeBasis j)‖ := by
      simp only [derivativeCoordinate, ContinuousLinearMap.sub_apply, Real.norm_eq_abs]
    _ ≤ ‖F - G‖ * ‖spacetimeBasis j‖ := (F - G).le_opNorm _
    _ = _ := by simp [spacetimeBasis, PiLp.norm_single]

theorem derivative_spatial_distance
    (F G : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    ‖derivativeSpatialRow F - derivativeSpatialRow G‖ ≤ 2 * ‖F - G‖ := by
  calc
    _ ≤ ∑ j, |(derivativeSpatialRow F - derivativeSpatialRow G) j| :=
      Native.euclidean_norm_le_sum_abs _
    _ = |derivativeCoordinate F 1 - derivativeCoordinate G 1| +
        |derivativeCoordinate F 2 - derivativeCoordinate G 2| := by
      simp [derivativeSpatialRow, Fin.sum_univ_two]
    _ ≤ _ := add_le_add (derivative_coordinate_distance F G 1)
      (derivative_coordinate_distance F G 2) |>.trans_eq (by ring)

theorem derivative_norm_le_row (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    ‖F‖ ≤ |derivativeCoordinate F 0| + 2 * ‖derivativeSpatialRow F‖ := by
  apply F.opNorm_le_bound (by positivity)
  intro x
  have hcoord₁ : |derivativeCoordinate F 1| ≤ ‖derivativeSpatialRow F‖ :=
    PiLp.norm_apply_le (derivativeSpatialRow F) 0
  have hcoord₂ : |derivativeCoordinate F 2| ≤ ‖derivativeSpatialRow F‖ :=
    PiLp.norm_apply_le (derivativeSpatialRow F) 1
  rw [Real.norm_eq_abs, derivative_apply_eq_sum]
  calc
    _ ≤ ∑ j, |derivativeCoordinate F j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |derivativeCoordinate F j| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (abs_nonneg _)
    _ = (|derivativeCoordinate F 0| + |derivativeCoordinate F 1| +
        |derivativeCoordinate F 2|) * ‖x‖ := by
      simp only [Fin.sum_univ_three]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x)

/-- Directional tests for the actual varying derivative, together with
an operator-norm freeze bound, control its frozen spatial gradient and
full derivative. The strip cap and the tested mass use the SAME original
law. In applications `F ω` is `fderiv ℝ f (z ω)`. -/
theorem derivative_bound_from_original_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V) (S : Set Ω)
    (F : Ω → EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (F₀ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (W : Ω → ℝ)
    {δ K E e B : ℝ} {threshold : ENNReal}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hE : 0 ≤ E) (he : 0 ≤ e) (hB : 0 ≤ B)
    (hbreadth : ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
      μ (V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold)
    (hmass : threshold < μ S)
    (hspeed : ∀ ω ∈ S, ‖V ω‖ ≤ B)
    (hhidden : ∀ ω ∈ S, |W ω| ≤ K)
    (htest : ∀ ω ∈ S, |F ω (spacetimeDirection (V ω)) - W ω| ≤ E)
    (hfreeze : ∀ ω ∈ S, ‖F ω - F₀‖ ≤ e) :
    let R := K + E + e + B * (2 * e)
    ‖derivativeSpatialRow F₀‖ ≤ R / δ ∧ ‖F₀‖ ≤ R + (B + 2) * (R / δ) := by
  let R := K + E + e + B * (2 * e)
  obtain ⟨hb, ha⟩ := gradient_row_bound_from_nearby_tests μ V hV S
    (fun ω => derivativeCoordinate (F ω) 0) W (fun ω => derivativeSpatialRow (F ω))
    hδ hK hE he (show 0 ≤ 2 * e by positivity) hB hbreadth hmass hspeed hhidden
    (by intro ω hω; simpa only [derivative_spacetime_direction] using htest ω hω)
    (fun ω hω => (derivative_coordinate_distance (F ω) F₀ 0).trans (hfreeze ω hω))
    (fun ω hω => (derivative_spatial_distance (F ω) F₀).trans
      (mul_le_mul_of_nonneg_left (hfreeze ω hω) (by norm_num)))
  refine ⟨hb, ?_⟩
  calc
    _ ≤ |derivativeCoordinate F₀ 0| + 2 * ‖derivativeSpatialRow F₀‖ := derivative_norm_le_row F₀
    _ ≤ _ := by nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
