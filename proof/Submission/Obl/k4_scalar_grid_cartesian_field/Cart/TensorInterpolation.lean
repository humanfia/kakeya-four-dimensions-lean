-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/TensorInterpolation.lean;
-- only the namespace was renamed into o230's.
import Submission.Lib.K4ScalarActualSwitching.TensorInterpolation
import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

export Submission.Lib.K4ScalarActualSwitching (
  polynomialOnCoordinate eval_polynomialOnCoordinate totalDegree_polynomialOnCoordinate tensorInterpolant eval_tensorInterpolant totalDegree_tensorInterpolant polynomial_eval_eq_lagrange lagrange_approximation_error tensor_interpolation_error lagrange_basis_eval_bound lagrange_weight_sum_bound tensor_interpolant_eval_bound
)

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
