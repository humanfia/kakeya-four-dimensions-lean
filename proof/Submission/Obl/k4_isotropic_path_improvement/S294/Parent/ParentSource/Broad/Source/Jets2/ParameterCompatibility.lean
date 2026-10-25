-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.ParameterCompatibility, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/ParameterCompatibility.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Reuse the existing qualification definitions under the original source
namespace. The implementations and provenance are in Qualification/. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterZoom
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicParameterBins
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CanonicalParameterWorlds

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2

export Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2 (
  zoomCoefficients measurable_zoomCoefficients zx_zoom zy_zoom
  zv_zoom zR_zoom zoom_coefficients_bound zoom_piece_diameter
  zoom_residual_decomposition zoom_residual_near_original_state zoom_residual_original_state_range parameterCode
  measurable_parameterCode dyadicParameterWidth dyadicParameterWidth_pos coarsenParameterCode
  coarsen_parameterCode original_parameter_fiber_subset exists_dyadicParameterWidth parameterLevel
  parameterLevel_width zoomParameterPiece measurable_zoomParameterPiece zoomParameterPiece_diameter
  parameterCenter original_parameter_center_distance original_parameter_center_bound original_parameter_zoom_coefficients_bound
  original_parameter_worlds_finite)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
