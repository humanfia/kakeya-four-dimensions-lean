-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ClockIsotropicCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ClockIsotropicCensus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Shared clock census accepted by the gate as K4ClockIsotropicSupport
(g00973), adapted from this LOT tree o265/x0943 e0bf23d4. -/
import Submission.Lib.K4ClockIsotropicSupport

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
export Submission.Lib.K4ClockIsotropicSupport (
  coarsenProductBase product_gridCode_dyadic_base
  clock_isotropic_support_from_joint_census exists_clock_coarsening_steps
  clock_isotropic_support_with_precision_margin)
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
