-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.Accepted, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The relative routes to o265 with the accepted o295 and o288 plugged in (session x1088).

o295 (`Submission.k4_physical_row_packet_potential`) is accepted; its frozen statement is
definitionally `Route265.RowPotentialAssertion`.  With it and the accepted o288, o265's staged
statement (`StagedWeakAssertion`, definitionally o265's frozen statement) needs only ONE of the
producer contracts below; the team's target is x1080's natural-unit contract
`RelRowCoreNatSourceAssertion` (`Tangent.NaturalCore`). -/
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.RowBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.NaturalCore
import Submission.Obl.k4_isotropic_path_improvement.S294.Route265.Glue
import Submission.Obl.k4_physical_row_packet_potential

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split

/-- The accepted o295, in the named form. -/
theorem rowPotential_accepted :
    Submission.Obl.k4_isotropic_path_improvement.S294.Route265.RowPotentialAssertion :=
  Submission.k4_physical_row_packet_potential

/-- **o265 from x1080's natural-unit relative row core source alone** (the team's target). -/
theorem staged_of_rel_row_core_nat (hR : RelRowCoreNatSourceAssertion) : StagedWeakAssertion :=
  staged_of_rel_row_core_nat_source hR Submission.k4_physical_parent_potential_candidates

/-- **o265 from x1080's relative row source alone** (`Tangent.RelativeSource`). -/
theorem staged_of_rel_row (hR : RelRowSourceAssertion) : StagedWeakAssertion :=
  staged_of_rel_row_source hR Submission.k4_physical_parent_potential_candidates

/-- **o265 from the scaled (x1078 `vFrame`) row-packet source alone.** -/
theorem staged_of_virtual_row_source (hVR : VirtualRowSourceAssertion) :
    StagedWeakAssertion :=
  staged_of_rows_and_virtual_row_source rowPotential_accepted hVR
    Submission.k4_physical_parent_potential_candidates

/-- **o265 (in o288's readable form) from x1088's relative-instance source alone.** -/
theorem staged_of_relative_source_accepted
    (hsrc : Submission.Obl.k4_isotropic_path_improvement.S294.Route265.RelativeSourceAssertion) :
    Submission.Obl.k4_physical_parent_potential_candidates.StagedAssertion :=
  Submission.Obl.k4_isotropic_path_improvement.S294.Route265.staged_of_rows_and_relative_source
    rowPotential_accepted hsrc

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
