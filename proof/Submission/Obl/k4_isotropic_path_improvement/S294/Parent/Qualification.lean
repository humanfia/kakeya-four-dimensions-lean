-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- The two-tangent scalar-normal qualification kernel is adapted, with
per-file attribution, from this LOT tree o265/x1030 at c13f2967e10c.
The accepted scalar analytic backend is imported throughout. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeQualification
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2HigherJets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalScalarNormalWorld

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

/-- The two-tangent qualification conclusion follows from the checked
higher-jet construction. Its scalar-normal hypotheses remain explicit. -/
theorem nativeQualificationStatement : NativeQualificationStatement :=
  nativeQualificationStatement_of_higherJets
    Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2.v2_higherJetsStatement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
