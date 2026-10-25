-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.Interface, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/Interface.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- The source geometry and qualification layers use the same scalar-normal
interface. Import its checked implementation once, preserving the source
namespace as a compatibility export. The original interface is attributed
in Qualification/Jets2/Interface.lean. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2

export Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2 (
  zx zy zv zS zR zpos dyadicBlock InCube ScalarNormal JetFit HigherJetsStatement)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
