-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/StarSelection.lean;
-- only the namespace was renamed into o230's.
import Submission.Lib.K4ScalarActualSwitching.StarSelection
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.Resampling

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

export Submission.Lib.K4ScalarActualSwitching (
  starSample starPair measurable_starPair measurePreserving_starPair controlPencil measurableSet_controlPencil pair_pencil_mass_le starBad measurableSet_starBad four_sample_pencil_mass_le starKernel starKernel_markov starKernel_apply star_retained_mass
)

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
