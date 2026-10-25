-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/SwitchPath.lean;
-- only the namespace was renamed into o230's.
import Submission.Lib.K4ScalarSwitching.SwitchPath
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching
import Submission.Lib.K4PolynomialPotential

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching

export Submission.Lib.K4ScalarSwitching.Switching (
  upperSubst eval_upperSubst eval_upperSubst_zero partial_upperSubst
  upperPrimitive eval_upperPrimitive_zero partial_upperPrimitive eval_partial_upperPrimitive_zero
  eval_second_upperPrimitive_zero legPoint eval_legPoint_zero partial_legPoint_control
  partial_legPoint_aux eval_substitution legField eval_partial_legField_control
  eval_partial_legField_aux brokenHeight brokenHeight_hessian brokenHeight_curl_bound
  exists_large_minor_coefficient eval_auxCoordinate eval_upperPrimitive_integral eval_legPoint
  eval_brokenHeight
)

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching
