-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/TensorRemez.lean;
-- only the namespace was renamed into o230's.
import Submission.Lib.K4ScalarSwitching.TensorRemez
import Submission.Lib.K4PolynomialRemez
import Submission.Lib.K4PolynomialPotential.Coordinate

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching

export Submission.Lib.K4ScalarSwitching.Switching (
  SquarePoint unitSquare product_square_remez pairCoordinates
  splitFour splitFour_symm_apply splitFour_apply volume_preserving_splitFour
  splitFour_mem_unit coordinate_line_witness polynomial_remez_four
)

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching
