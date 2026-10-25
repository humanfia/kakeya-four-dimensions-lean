-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.UnshearedCapNumerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/UnshearedCapNumerics.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/UnshearedCapNumerics.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.CapExponentNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open scoped ENNReal

/-- The unsheared Jacobian loss can be absorbed in the source tolerance. -/
theorem unsheared_cap_coefficient_shift {N κ K fOld fNew τ ε E : ℝ}
    (hN : 0 < N) (hκ : 0 ≤ κ) :
    (ENNReal.ofReal (N^(-fNew+τ+ε))*ENNReal.ofReal (64*(max κ K)^2))*
        ENNReal.ofReal ((κ*N^E)*N^fOld) =
      (ENNReal.ofReal (N^(-fNew+(τ+E)+ε))*ENNReal.ofReal (64*(max κ K)^2))*
        ENNReal.ofReal (κ*N^fOld) := by
  have hr : N^(-fNew+(τ+E)+ε)=N^(-fNew+τ+ε)*N^E := by
    rw [←Real.rpow_add hN]
    congr 1
    ring
  rw [hr]
  rw [ENNReal.ofReal_mul (mul_nonneg hκ (Real.rpow_nonneg hN.le E)),
    ENNReal.ofReal_mul hκ,
    ENNReal.ofReal_mul (Real.rpow_nonneg hN.le (-fNew+τ+ε)),
    ENNReal.ofReal_mul hκ]
  ring

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
