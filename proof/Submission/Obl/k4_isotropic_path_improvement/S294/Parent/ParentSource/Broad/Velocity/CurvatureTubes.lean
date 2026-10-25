-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.CurvatureTubes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/CurvatureTubes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/CurvatureTubes.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.AnisotropicTubes

/-!
# Tangent tubes from curvature alone

These variants of the own TangentTubes/AnisotropicTubes argument use the
leading quadratic coefficient directly. The affine and constant signal
terms can be arbitrary. The earlier files are adapted from this LOT
tree o106/x0352, commits 5bf2ec7212f0 and d78c43c7c261; their underlying
exact quadratic remainder and lattice lemmas are imported.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open SourceGeometry Set
open Submission.Obl.k4_mk_grid_transfer
noncomputable section

theorem quadratic_unit_tangent_change_of_curvature
    (v : Fin 3 → ℝ) (a b K s t : ℝ) (hv : v 0=1) (ha : |a|≤8*K) :
    ‖unitTangent (liftedVector v (2*a*t+b))-
      unitTangent (liftedVector v (2*a*s+b))‖≤32*K*|t-s| := by
  have hs : liftedVector v (2*a*s+b)≠0 := norm_pos_iff.mp
    (lt_of_lt_of_le zero_lt_one (norm_liftedVector_ge_one v _ hv))
  have hh := unitTangent_sub_bound (liftedVector v (2*a*t+b))
    (liftedVector v (2*a*s+b)) (norm_liftedVector_ge_one v _ hv) hs
  rw [norm_liftedVector_sub] at hh
  have heq : (2*a*t+b)-(2*a*s+b)=(2*a)*(t-s) := by ring
  rw [heq,abs_mul,abs_mul] at hh
  norm_num at hh
  have hm := mul_le_mul_of_nonneg_right ha (abs_nonneg (t-s))
  nlinarith

theorem quadraticLift_tangent_bound_of_curvature
    (p v : Fin 3 → ℝ) (a b c K s t : ℝ) (ha : |a|≤8*K) :
    ‖quadraticLift p v a b c t-quadraticLift p v a b c s-
      (t-s) • liftedVector v (2*a*s+b)‖≤8*K*|t-s|^2 := by
  rw [quadraticLift_tangent_remainder,norm_smul]
  simpa [abs_mul,abs_pow] using mul_le_mul_of_nonneg_right ha (sq_nonneg (t-s))

theorem quadraticLift_lattice_tangent_tube_of_curvature
    (p v : Fin 3 → ℝ) (a b c K width fine s t : ℝ)
    (hK : 0≤K) (hfine : 0<fine) (hv : v 0=1) (ha : |a|≤8*K)
    (hdt : |t-s|≤width) (hsmall : 8*K*width^2<fine)
    (z : Fin 4 → ℤ) (hcell : fine⁻¹ • quadraticLift p v a b c t∈latticeCell z) :
    latticePoint z∈lineTube 3 (fine⁻¹ • quadraticLift p v a b c s)
      (unitTangent (liftedVector v (2*a*s+b))) := by
  have hd : liftedVector v (2*a*s+b)≠0 := norm_pos_iff.mp
    (lt_of_lt_of_le zero_lt_one (norm_liftedVector_ge_one v _ hv))
  apply lattice_cell_mem_tangent_tube (by decide) (by decide)
    (quadraticLift p v a b c s) (liftedVector v (2*a*s+b))
    (quadraticLift p v a b c t) (t-s) fine hfine hd z hcell
  have hrem := quadraticLift_tangent_bound_of_curvature p v a b c K s t ha
  have hsq := pow_le_pow_left₀ (abs_nonneg (t-s)) hdt 2
  exact (hrem.trans (mul_le_mul_of_nonneg_left hsq (by positivity))).trans_lt hsmall

/-- Independent base/height meshes, with no restriction on the constant
or affine height coefficient. -/
theorem anisotropic_quadratic_lattice_tangent_tube_of_curvature
    (pos vel : Fin 3 → ℝ) (a b c K width baseMesh hidden s t : ℝ)
    (hK : 0≤K) (hp : 0<baseMesh) (hb : 0<hidden) (hv : vel 0=1)
    (ha : |a|≤8*K) (hdt : |t-s|≤width) (hsmall : 8*K*width^2<hidden)
    (z : Fin 4 → ℤ)
    (hcell : baseMesh⁻¹ • heightScale (baseMesh/hidden)
      (quadraticLift pos vel a b c t)∈latticeCell z) :
    latticePoint z∈lineTube 3
      (baseMesh⁻¹ • heightScale (baseMesh/hidden) (quadraticLift pos vel a b c s))
      (heightUnit (baseMesh/hidden) (unitTangent (liftedVector vel (2*a*s+b)))) := by
  let compression := baseMesh/hidden
  have hc : 0<compression := div_pos hp hb
  have hscaled : |compression*a|≤8*(compression*K) := by
    rw [abs_mul,abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left ha hc.le).trans_eq (by ring)
  have herror : 8*(compression*K)*width^2<baseMesh := by
    have hh := mul_lt_mul_of_pos_left hsmall hc
    dsimp [compression] at hh ⊢
    field_simp at hh ⊢
    nlinarith
  rw [heightScale_quadraticLift] at hcell ⊢
  have hdir : liftedVector vel (2*(compression*a)*s+compression*b)=
      heightScale compression (liftedVector vel (2*a*s+b)) := by
    ext j
    fin_cases j <;> simp [heightScale,liftedVector] <;> ring
  have hne : liftedVector vel (2*a*s+b)≠0 := norm_pos_iff.mp
    (lt_of_lt_of_le zero_lt_one (norm_liftedVector_ge_one vel _ hv))
  have hfit := quadraticLift_lattice_tangent_tube_of_curvature pos vel
    (compression*a) (compression*b) (compression*c) (compression*K)
    width baseMesh s t (mul_nonneg hc.le hK) hp hv hscaled hdt herror z hcell
  rw [hdir,unitTangent_heightScale_unitTangent hc.ne' _ hne] at hfit
  exact hfit

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
