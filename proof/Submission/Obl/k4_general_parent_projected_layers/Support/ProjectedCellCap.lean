/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ProjectedCellCap.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.MeshProjection
import Submission.Lib.K4MovingMeshBoxes.Projection
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Compatibility names for the accepted moving-mesh geometry library. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

noncomputable section

abbrev basePoint := @Submission.Lib.K4MovingMeshBoxes.basePoint
abbrev projectedCell := @Submission.Lib.K4MovingMeshBoxes.projectedCell
abbrev majorGroup := @Submission.Lib.K4MovingMeshBoxes.majorGroup
abbrev projectedCell_mem_movingBox := @Submission.Lib.K4MovingMeshBoxes.projectedCell_mem_movingBox
abbrev projected_cell_cap := @Submission.Lib.K4MovingMeshBoxes.projected_cell_cap

end

end Submission.Obl.k4_general_parent_projected_layers
