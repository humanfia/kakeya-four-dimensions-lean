/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/AffineMeshCap.lean. -/
import Submission.Lib.K4AffineMeshCaps.Transport
import Submission.Lib.K4AffineMeshCaps.Saturation
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Compatibility names for the gate-accepted K4AffineMeshCaps library (g00673). -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

abbrev affineBase := @Submission.Lib.K4AffineMeshCaps.affineBase
abbrev measurable_affineBase := @Submission.Lib.K4AffineMeshCaps.measurable_affineBase
abbrev map_affineBase_volume := @Submission.Lib.K4AffineMeshCaps.map_affineBase_volume
abbrev volume_affineBase_preimage := @Submission.Lib.K4AffineMeshCaps.volume_affineBase_preimage
abbrev affineBase_coordinate_variation := @Submission.Lib.K4AffineMeshCaps.affineBase_coordinate_variation
abbrev affine_mesh_cell_cap := @Submission.Lib.K4AffineMeshCaps.affine_mesh_cell_cap
abbrev base_cell_cap_of_bounded_signal := @Submission.Lib.K4AffineMeshCaps.base_cell_cap_of_bounded_signal

end Submission.Obl.k4_general_parent_projected_layers
