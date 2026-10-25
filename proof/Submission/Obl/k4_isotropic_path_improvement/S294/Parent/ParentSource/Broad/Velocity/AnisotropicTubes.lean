-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.AnisotropicTubes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/AnisotropicTubes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/AnisotropicTubes.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.HeightScale
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.TangentTubes

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
open Submission.Obl.k4_mk_grid_transfer
open Set

noncomputable section

theorem heightScale_smul (a r : ℝ) (x : Space) :
    heightScale a (r • x) = r • heightScale a x := by
  ext j
  by_cases hj : j = 3 <;> simp [heightScale, hj, mul_left_comm]

theorem heightScale_quadraticLift (compression : ℝ) (p v : Fin 3 → ℝ)
    (a b c t : ℝ) :
    heightScale compression (quadraticLift p v a b c t) =
      quadraticLift p v (compression * a) (compression * b) (compression * c) t := by
  ext j
  fin_cases j <;> simp [heightScale, quadraticLift, liftedVector] <;> ring

theorem unitTangent_heightScale_unitTangent {a : ℝ} (ha : a ≠ 0)
    (x : Space) (hx : x ≠ 0) :
    unitTangent (heightScale a x) = heightUnit a (unitTangent x) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [heightUnit, unitTangent, heightScale_smul, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, smul_smul, mul_inv_rev, inv_inv]
  congr 1
  field_simp

/-- The tangent error is paid by the hidden width, independently of how
fine the three-dimensional base mesh is. -/
theorem anisotropic_quadratic_lattice_tangent_tube
    (pos vel : Fin 3 → ℝ) (a b c K width baseMesh hidden s t : ℝ)
    (hK : 0 ≤ K) (hp : 0 < baseMesh) (hb : 0 < hidden) (hv : vel 0 = 1)
    (h : ∀ u ∈ Icc (0 : ℝ) 1, |a * u ^ 2 + b * u + c| ≤ K)
    (hdt : |t - s| ≤ width) (hsmall : 8 * K * width ^ 2 < hidden)
    (z : Fin 4 → ℤ)
    (hcell : baseMesh⁻¹ • heightScale (baseMesh / hidden)
      (quadraticLift pos vel a b c t) ∈ latticeCell z) :
    latticePoint z ∈ lineTube 3
      (baseMesh⁻¹ • heightScale (baseMesh / hidden) (quadraticLift pos vel a b c s))
      (heightUnit (baseMesh / hidden) (unitTangent (liftedVector vel (2 * a * s + b)))) := by
  let compression := baseMesh / hidden
  have hc : 0 < compression := div_pos hp hb
  have hscaled : ∀ u ∈ Icc (0 : ℝ) 1,
      |(compression * a) * u ^ 2 + (compression * b) * u + compression * c| ≤ compression * K := by
    intro u hu
    rw [show (compression * a) * u ^ 2 + (compression * b) * u + compression * c =
      compression * (a * u ^ 2 + b * u + c) by ring, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (h u hu) hc.le
  have herror : 8 * (compression * K) * width ^ 2 < baseMesh := by
    have hh := mul_lt_mul_of_pos_left hsmall hc
    dsimp [compression] at hh ⊢
    field_simp at hh ⊢
    nlinarith
  rw [heightScale_quadraticLift] at hcell ⊢
  have hdir : liftedVector vel (2 * (compression * a) * s + compression * b) =
      heightScale compression (liftedVector vel (2 * a * s + b)) := by
    ext j
    fin_cases j <;> simp [heightScale, liftedVector] <;> ring
  have hne : liftedVector vel (2 * a * s + b) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (norm_liftedVector_ge_one _ _ hv))
  have hfit := quadraticLift_lattice_tangent_tube pos vel
    (compression * a) (compression * b) (compression * c) (compression * K)
    width baseMesh s t (mul_nonneg hc.le hK) hp hv hscaled hdt herror z hcell
  rw [hdir, unitTangent_heightScale_unitTangent hc.ne' _ hne] at hfit
  exact hfit

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
