-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/DeterminantBreadth.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/DeterminantBreadth.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/DeterminantBreadth.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Lib.K4DeterminantBreadth

/-!
Compatibility names for the determinant-breadth kernel originally adapted
with attribution from LOT o106/x0358, commit 6bfc742. The kernel is now an
accepted library contribution, so this module imports its proofs.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian.Breadth

export Submission.Lib.K4DeterminantBreadth
  (abs_det_ge_prod_infDist Good image_Iio_castSucc_snoc image_Iio_last_snoc
    good_snoc_iff sum_snoc good_weight det_weight_of_breadth)

end Submission.Obl.k4_physical_row_packet_potential.Cartesian.Breadth
