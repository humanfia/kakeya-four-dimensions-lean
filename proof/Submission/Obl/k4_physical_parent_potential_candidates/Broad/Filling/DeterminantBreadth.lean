-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Filling/DeterminantBreadth.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o106, branch x0352, commit dcdf5bd50e74;
-- source Submission/Obl/k4_isotropic_path_improvement/DeterminantBreadth.lean (session x0352).
-- Existing source attributions are preserved below.

import Submission.Lib.K4DeterminantBreadth

/-!
Compatibility names for the determinant-breadth kernel originally adapted
with attribution from LOT o106/x0358, commit 6bfc742. The kernel is now an
accepted library contribution, so this module imports its proofs.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling.Breadth

export Submission.Lib.K4DeterminantBreadth
  (abs_det_ge_prod_infDist Good image_Iio_castSucc_snoc image_Iio_last_snoc
    good_snoc_iff sum_snoc good_weight det_weight_of_breadth)

end Submission.Obl.k4_physical_parent_potential_candidates.Broad.Filling.Breadth
