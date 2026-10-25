-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.RelativeGradientJets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/RelativeGradientJets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/RelativeGradientJets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/RelativeGradientJets.lean. Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/RelativeGradientJets.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.HessianCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Interface
import Submission.Obl.k4_profile_density_bounds.Support

/-! # Relative coordinate-gradient jets from the frozen value norming clause -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric

noncomputable section

/-- The value-norming clause of the frozen dense-jet hypothesis. This is
supplied by its FIRST field; no additional geometric norming assertion is
introduced. The extension predicate is the exact frozen `exf`. -/
def ValueJetBound (D J : ℕ) : Prop :=
  ∀ (A : ℝ), 2 ≤ A → ∀ g : EuclideanSpace ℝ (Fin 3) → ℝ, exf D g →
    ∀ (E : Set (EuclideanSpace ℝ (Fin 3))) (v : ℝ), MeasurableSet E →
      E ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 →
      ENNReal.ofReal A⁻¹ ≤ volume E → 0 ≤ v → (∀ x ∈ E, |g x| ≤ v) →
      ∀ j : ℕ, j ≤ 6 → ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        ‖iteratedFDeriv ℝ j g x‖ ≤ A ^ J * v

/-- An actual coordinate value is bounded by the norm of its own gradient. -/
theorem gradientComponent_abs_le_norm
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (j : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    |gradientComponent g j x| ≤ ‖fderiv ℝ g x‖ := by
  simpa [gradientComponent, derivativeCoordinate, spacetimeBasis] using
    (fderiv ℝ g x).le_opNorm (spacetimeBasis j)

/-- The same value-jet clause norms the actual gradient from a substantial
measurable set. Later original-law applications supply its volume through
the EARLIER entry floor and original continuous base cap. -/
theorem gradient_norm_from_value_jets_on_set
    {D J : ℕ} (hjets : ValueJetBound D J)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : ∀ j : Fin 3, exf D (gradientComponent g j))
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E)
    (hEball : E ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {A v : ℝ} (hA : 2 ≤ A) (hvolume : ENNReal.ofReal A⁻¹ ≤ volume E)
    (hv : 0 ≤ v) (hsmall : ∀ x ∈ E, ‖fderiv ℝ g x‖ ≤ v) :
    ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ g x‖ ≤ 3 * A ^ J * v := by
  intro x hx
  apply (derivative_norm_le_three_coordinates _ (C := A ^ J * v) (by positivity) ?_).trans_eq (by ring)
  intro j
  have hh := hjets A hA (gradientComponent g j) (hg j) E v hE hEball hvolume hv
    (fun y hy => (gradientComponent_abs_le_norm g j y).trans (hsmall y hy)) 0 (by norm_num) x hx
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, gradientComponent] using hh

/-- Norming the coordinate gradients on a fixed real cube derives their
first jets relative to the ACTUAL global gradient bound. The constant8
is universal, from a cube of volume1/8 inside the unit ball. -/
theorem coordinate_gradient_jets_relative_to_gradient
    {D J : ℕ} (hjets : ValueJetBound D J)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : ∀ j : Fin 3, exf D (gradientComponent g j))
    {M : ℝ} (hM : 0 ≤ M)
    (hglobal : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2, ‖fderiv ℝ g x‖ ≤ M) :
    ∀ j : Fin 3, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ (gradientComponent g j) x‖ ≤ (8 : ℝ) ^ J * M := by
  let Q := k4_profile_density_bounds.baseBox (0 : EuclideanSpace ℝ (Fin 4)) (1 / 4)
  have hQ : MeasurableSet Q := k4_profile_density_bounds.measurableSet_baseBox _ _
  have hQball : Q ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro x hx
    have hcoord := (k4_profile_density_bounds.mem_baseBox_iff _ _ x).mp hx
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖x‖ ≤ ∑ j, |x j| := Native.euclidean_norm_le_sum_abs _
      _ ≤ ∑ _j : Fin 3, (1 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [PiLp.zero_apply, sub_zero] using hcoord j
      _ ≤ 1 := by norm_num
  have hQvolume : ENNReal.ofReal ((8 : ℝ)⁻¹) ≤ volume Q := by
    dsimp only [Q]
    rw [k4_profile_density_bounds.volume_baseBox _ _ (by norm_num)]
    norm_num
  intro j x hx
  have hh := hjets 8 (by norm_num) (gradientComponent g j) (hg j) Q M hQ hQball hQvolume hM
    (fun y hy => (gradientComponent_abs_le_norm g j y).trans
      (hglobal y (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) (hQball hy))))
    1 (by norm_num) x hx
  simpa only [norm_iteratedFDeriv_one] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
