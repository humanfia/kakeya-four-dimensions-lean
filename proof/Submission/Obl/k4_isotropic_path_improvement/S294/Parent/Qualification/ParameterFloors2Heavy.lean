-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ParameterFloors2Heavy, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ParameterFloors2Heavy.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ParameterFloors2Heavy.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ParameterFloors2Heavy.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 4c91e1da. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterFloors2Lower
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterFloor

/-!
# x0352's floor cleanup discharges `FloorCleanupStatement`

`FloorCleanupStatement d c ε` is the statement of x0352's `coefficient_floor_cleanup_scaled`
(o106, `ParameterFloor.lean`, built on the accepted scalar clustering
`Submission.k4_scalar_coefficient_clustering`), with `lightBlocks` = x0352's
`lightCoefficientBlocks`.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

theorem floorCleanupStatement_holds (d c ε : ℝ) (hd : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c)
    (hε : 0 < ε) : FloorCleanupStatement d c ε :=
  Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.coefficient_floor_cleanup_scaled d c ε hd hd1 hc hε

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
