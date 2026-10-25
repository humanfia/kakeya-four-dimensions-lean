/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/MeshProjection.lean. -/
import Submission.Lib.K4MovingMeshBoxes.Geometry
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Compatibility names for the accepted moving-mesh geometry library. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

noncomputable section

abbrev interval_mesh_cover := @Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover
abbrev baseMesh := @Submission.Lib.K4MovingMeshBoxes.baseMesh
abbrev movingBox := @Submission.Lib.K4MovingMeshBoxes.movingBox
abbrev movingBox_mesh_cover := @Submission.Lib.K4MovingMeshBoxes.movingBox_mesh_cover
abbrev movingBox_mesh_volume := @Submission.Lib.K4MovingMeshBoxes.movingBox_mesh_volume
abbrev measure_movingBox_of_cell_cap := @Submission.Lib.K4MovingMeshBoxes.measure_movingBox_of_cell_cap

theorem measurable_baseMesh (delta : ℝ) : Measurable (baseMesh delta) := by
  unfold baseMesh Submission.Lib.K4MovingMeshBoxes.baseMesh
  fun_prop

end

end Submission.Obl.k4_general_parent_projected_layers
