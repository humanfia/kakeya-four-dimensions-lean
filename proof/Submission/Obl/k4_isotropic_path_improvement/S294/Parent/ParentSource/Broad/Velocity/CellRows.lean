-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.CellRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/CellRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/CellRows.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit d78c43c7c261;
-- source Submission/Obl/k4_isotropic_path_improvement/CellRows.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.MeasureBasis
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling.MeasureCapture
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.TangentTubes

/-!
Choose the physical velocity row separately on each finite state. The
resulting row field and reference event are measurable, and the original
incidence law pays for all captured-state losses.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set Module
open SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling
open scoped Pointwise

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Distance to a subspace scales exactly with the norm of a non-normalized
lifted velocity, including the zero vector. -/
theorem infDist_unitTangent {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (d : EuclideanSpace ℝ (Fin n)) :
    Metric.infDist d (V : Set _) = ‖d‖ * Metric.infDist (unitTangent d) (V : Set _) := by
  by_cases hd : d = 0
  · subst d
    simp only [norm_zero, zero_mul]
    exact Metric.infDist_zero_of_mem V.zero_mem
  · have hn : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    have hset : ‖d‖ • (V : Set (EuclideanSpace ℝ (Fin n))) = V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact V.smul_mem _ hy
      · intro hx
        refine ⟨‖d‖⁻¹ • x, V.smul_mem _ hx, ?_⟩
        simp only [smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h := infDist_smul₀ hn (V : Set _) (unitTangent d)
    rw [hset] at h
    have hrec : ‖d‖ • unitTangent d = d := by
      simp only [unitTangent, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [hrec, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg d)] at h
    exact h

/-- Unit-direction plane capture implies capture of bounded raw velocities. -/
theorem raw_plane_distance_bound {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (d : EuclideanSpace ℝ (Fin n))
    (K ε : ℝ) (hnorm : ‖d‖ ≤ K)
    (hnear : Metric.infDist (unitTangent d) (V : Set _) ≤ ε) :
    Metric.infDist d (V : Set _) ≤ K * ε := by
  rw [infDist_unitTangent]
  exact mul_le_mul hnorm hnear Metric.infDist_nonneg ((norm_nonneg d).trans hnorm)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
