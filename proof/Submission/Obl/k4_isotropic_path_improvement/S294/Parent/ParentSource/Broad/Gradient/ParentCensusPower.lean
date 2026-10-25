-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ParentCensusPower, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ParentCensusPower.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ParentCensusPower.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentFramePower
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ProfileMeshPowerBudget

/-! # Independent physical base/height meshes have a uniform census power -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

/-- Combine the actual unsheared joint count with profile matching at the height
mesh. The base and height resolutions may be different. -/
theorem physical_parent_joint_census_le_power
    {N K κ C sizeLoss count base hidden depthOld depthFine fOld fFine dimension error : ℝ}
    (hN : 2 ≤ N) (hK : 2304 ≤ K) (hκ : 0 ≤ κ) (hκK : κ ≤ K)
    (hC : 0 ≤ C) (u v R : ℕ) (hCK : C ≤ K ^ (u + 12))
    (hsize : 0 ≤ sizeLoss) (hsizeK : sizeLoss ≤ K) (hhidden : 0 < hidden)
    (hdim : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (hprofile : fFine - fOld ≤ dimension * (depthFine - depthOld) + error)
    (herror : N ^ error ≤ K)
    (hscale : hidden ≤ K ^ v * (δ N depthFine / δ N depthOld))
    (hcount : count * base ^ 3 ≤
      62208 * C ^ 3 * K ^ (3 * R + 28) * κ ^ 4 * sizeLoss * N ^ (fFine - fOld)) :
    count * base ^ 3 * hidden ^ dimension ≤ K ^ (3 * u + 3 * R + v + 73) := by
  have hK0 : 0 ≤ K := by linarith
  have hcoefficient := physical_parent_count_coefficient_le_power hK hκ hκK hC
    (u + 12) R hCK hsize hsizeK
  have hprofileMesh := profile_mesh_power_budget hN (by linarith) hhidden hdim hdim1
    hprofile herror v hscale
  calc
    _ ≤ (62208 * C ^ 3 * K ^ (3 * R + 28) * κ ^ 4 * sizeLoss * N ^ (fFine - fOld)) *
        hidden ^ dimension := mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hhidden.le _)
    _ = (62208 * C ^ 3 * K ^ (3 * R + 28) * κ ^ 4 * sizeLoss) *
        (N ^ (fFine - fOld) * hidden ^ dimension) := by ring
    _ ≤ K ^ (3 * (u + 12) + 3 * R + 35) * K ^ (v + 2) :=
      mul_le_mul hcoefficient hprofileMesh
        (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ N) _)
          (Real.rpow_nonneg hhidden.le _)) (pow_nonneg hK0 _)
    _ = _ := by
      rw [← pow_add]
      congr 1
      omega

/-- The same estimate in the literal cardinality-over-mesh form. -/
theorem physical_parent_joint_census_div_bound
    {K count base hidden dimension : ℝ} {Q : ℕ} (hbase : 0 < base) (hhidden : 0 < hidden)
    (hcount : count * base ^ 3 * hidden ^ dimension ≤ K ^ Q) :
    count ≤ K ^ Q / (base ^ 3 * hidden ^ dimension) := by
  apply (le_div_iff₀ (mul_pos (pow_pos hbase _) (Real.rpow_pos_of_pos hhidden _))).mpr
  simpa only [mul_assoc] using hcount

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
