-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/SwitchSlice.lean;
-- only the namespace was renamed into o230's.
import Submission.Lib.K4ScalarSwitching.SwitchSlice
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.SwitchPath

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching

export Submission.Lib.K4ScalarSwitching.Switching (
  selectedControl sliceValues endpointSlice slicePoint
  eval_endpointSlice partial_endpointSlice slice_endpoint_jacobian
)

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Switching
