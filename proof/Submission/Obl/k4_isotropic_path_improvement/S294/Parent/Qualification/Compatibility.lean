-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.Compatibility, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/Compatibility.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/Compatibility.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.PlaneGraph
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.QuadraticTangents

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

export Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry (
  normal_base_bound
  final_normal_lower_bound
  exists_bounded_plane_row
  exists_bounded_plane_row_of_det
  unit_normal_l1_lower
  abs_inner_le_plane_distance
  liftedVector
  inner_liftedVector
  exists_unit_subspace_normal
  subspace_graph_row
  bounded_quadratic_coefficients
  quadratic_hasDerivAt
  quadratic_tangent_bounds
  quadraticLift
  quadraticLift_tangent_remainder
  quadraticLift_tangent_bound
  native_quadratic_tangents)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
