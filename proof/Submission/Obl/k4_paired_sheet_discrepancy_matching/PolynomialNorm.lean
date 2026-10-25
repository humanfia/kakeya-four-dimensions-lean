/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/PolynomialNorm.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Mathlib
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm

/-! Re-export the general polynomial comparison accepted by the gate as g00529. -/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching

export Submission.Lib.K4PolynomialRemezThree (
  coefficientMass
  coefficientMass_nonneg
  abs_coeff_le_coefficientMass
  exists_coefficient_bound_on_unit_cube
  card_support_le_degree_box
  norm_complex_eval_le_of_coeff_bound
  exists_complex_bound_from_real_cube
)

end Submission.Obl.k4_paired_sheet_discrepancy_matching
