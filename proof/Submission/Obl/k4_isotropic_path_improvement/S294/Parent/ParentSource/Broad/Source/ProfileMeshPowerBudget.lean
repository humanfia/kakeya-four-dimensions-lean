-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ProfileMeshPowerBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ProfileMeshPowerBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ProfileMeshPowerBudget.lean.
All earlier source attributions below are retained. -/
-- From this LOT tree, o265 session x0943, branch origin/x0943, Broad/Source/ProfileMeshPowerBudget.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SharpFramePowerBudget
import Submission.Obl.k4_finite_affine_parent_sources.SourceDensityGrid

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

/-- Matching the actual physical mesh to the original fine/old dyadic
width turns the original density-profile factor into the scalar power
mesh^(-dimension), with only explicit envelope losses. -/
theorem profile_mesh_power_budget
    {N K mesh depthOld depthFine fOld fFine dimension error : ℝ}
    (hN : 2 ≤ N) (hK : 2 ≤ K) (hmesh : 0 < mesh)
    (hdim : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (hprofile : fFine-fOld ≤ dimension*(depthFine-depthOld)+error)
    (herror : N^error ≤ K) (u : ℕ)
    (hscale : mesh ≤ K^u*(δ N depthFine/δ N depthOld)) :
    N^(fFine-fOld)*mesh^dimension ≤ K^(u+2) := by
  have hN1 : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hδOld : 0 < δ N depthOld :=
    (Real.rpow_pos_of_pos hNp _).trans_le
      (Submission.Obl.k4_horizon_chart_assembly.resolution_bounds hNp depthOld).1
  have hδ : δ N depthFine ≤ 2*N^(depthOld-depthFine)*δ N depthOld :=
    Submission.Obl.k4_finite_affine_parent_sources.density_grid_width_ratio
      (by linarith : 1 < N) (by linarith : depthOld ≤ depthFine+(depthOld-depthFine))
  have hratio : δ N depthFine/δ N depthOld ≤ 2*N^(-(depthFine-depthOld)) := by
    apply (div_le_iff₀ hδOld).mpr
    convert hδ using 1 <;> ring
  have hmeshBound : mesh ≤ 2*K^u*N^(-(depthFine-depthOld)) := by
    calc
      _ ≤ K^u*(δ N depthFine/δ N depthOld) := hscale
      _ ≤ K^u*(2*N^(-(depthFine-depthOld))) :=
        mul_le_mul_of_nonneg_left hratio (pow_nonneg hK0 _)
      _ = _ := by ring
  have hproduct : N^(depthFine-depthOld)*mesh ≤ 2*K^u := by
    calc
      _ ≤ N^(depthFine-depthOld)*(2*K^u*N^(-(depthFine-depthOld))) :=
        mul_le_mul_of_nonneg_left hmeshBound (Real.rpow_nonneg hNp.le _)
      _ = _ := by
        rw [Real.rpow_neg hNp.le]
        field_simp
  have hbase : 1 ≤ 2*K^u := by linarith [one_le_pow₀ hK1 (n:=u)]
  calc
    _ ≤ N^(dimension*(depthFine-depthOld)+error)*mesh^dimension :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 hprofile)
        (Real.rpow_nonneg hmesh.le _)
    _ = N^error*(N^(depthFine-depthOld)*mesh)^dimension := by
      rw [Real.rpow_add hNp,Real.mul_rpow (Real.rpow_nonneg hNp.le _) hmesh.le,
        ←Real.rpow_mul hNp.le]
      rw [mul_comm dimension (depthFine-depthOld)]
      ring
    _ ≤ K*(2*K^u)^dimension := by gcongr
    _ ≤ K*(2*K^u)^(1:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase hdim1) hK0
    _ = 2*K*K^u := by rw [Real.rpow_one]; ring
    _ ≤ K*K*K^u := by gcongr
    _ = _ := by simp only [pow_add]; ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
