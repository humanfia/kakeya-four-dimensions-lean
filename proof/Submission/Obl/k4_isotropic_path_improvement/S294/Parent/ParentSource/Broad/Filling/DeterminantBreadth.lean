-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Filling.DeterminantBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Filling/DeterminantBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Filling/DeterminantBreadth.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit dcdf5bd50e74;
-- source Submission/Obl/k4_isotropic_path_improvement/DeterminantBreadth.lean (session x0352).
-- Existing source attributions are preserved below.

import Submission.Lib.K4DeterminantBreadth

/-!
Compatibility names for the determinant-breadth kernel originally adapted
with attribution from LOT o106/x0358, commit 6bfc742. The kernel is now an
accepted library contribution, so this module imports its proofs.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling.Breadth

export Submission.Lib.K4DeterminantBreadth
  (abs_det_ge_prod_infDist Good image_Iio_castSucc_snoc image_Iio_last_snoc
    good_snoc_iff sum_snoc good_weight det_weight_of_breadth)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling.Breadth
