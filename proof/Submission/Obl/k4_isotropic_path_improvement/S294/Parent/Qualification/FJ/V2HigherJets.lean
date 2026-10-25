-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2HigherJets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2HigherJets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2HigherJets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2HigherJets.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2BlockFitKernel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Statement
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Assembly

set_option autoImplicit false

/-!
# The first jet and the higher jets in version 2

Paper `tex-05`, Prop. `prop:scalar-normal` and Prop. `prop:higher-jets` for `j = 2` (rows in
`(ℝ²)^*`), as needed by version 2 of Section 6 (`tex-06`, l. 17–18):

* `v2_firstJetStatement : Jets2.FirstJetStatement` (`FJ/V2Statement.lean`, with the planar kernel
  of `FJ/V2BlockFitKernel.lean`);
* `v2_higherJetsStatement : Jets2.HigherJetsStatement` (`Jets2/Assembly.lean`).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

theorem v2_firstJetStatement : FirstJetStatement :=
  firstJetStatement_of_range rangeFitStatement_holds

theorem v2_higherJetsStatement : HigherJetsStatement :=
  higher_jets_of_first_jet v2_firstJetStatement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
