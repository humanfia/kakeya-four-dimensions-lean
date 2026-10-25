-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/Switching.lean;
-- only the namespace was renamed into o230's.
import Submission.Lib.K4ScalarSwitching.Switching

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching

export Submission.Lib.K4ScalarSwitching.Switching (
  partials_commute partial_eval_zero_eq_coeff endpointMinor eval_endpointMinor
  hessian hessian_symm minorDerivative eval_partial_endpointMinor
  curl_minor_identity curl_bound_of_minor_derivatives polynomial_curl_bound exists_large_minor_derivative
  partial_aeval
)

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching
