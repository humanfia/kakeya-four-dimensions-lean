/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/GridLists.lean.
Its original attribution comments are retained below.
-/
import Submission.Lib.K4ScalarFiniteGuard.GridLists

/-! Compatibility names for the accepted shared grid-list library. -/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes

abbrev overlapBinEstimate := @Submission.Lib.K4ScalarFiniteGuard.overlapBinEstimate
noncomputable abbrev overlapBins := @Submission.Lib.K4ScalarFiniteGuard.overlapBins
abbrev overlapBins_card_le := @Submission.Lib.K4ScalarFiniteGuard.overlapBins_card_le
abbrev floor_mem_overlapBins := @Submission.Lib.K4ScalarFiniteGuard.floor_mem_overlapBins
abbrev power_overlapBins_card := @Submission.Lib.K4ScalarFiniteGuard.power_overlapBins_card
noncomputable abbrev transferGridList := @Submission.Lib.K4ScalarFiniteGuard.transferGridList
abbrev transferGridList_mem := @Submission.Lib.K4ScalarFiniteGuard.transferGridList_mem
abbrev measurableSet_transferGridList := @Submission.Lib.K4ScalarFiniteGuard.measurableSet_transferGridList
abbrev transferGridList_card := @Submission.Lib.K4ScalarFiniteGuard.transferGridList_card

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes
