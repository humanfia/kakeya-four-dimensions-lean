-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_restricted_uniform_improvement.Frostman.FinalQ.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain
import Submission.WZ.Obl.wz_separated_scales_gain

/-! The repaired o038 proof from the all-scales estimate, with independent
trichotomy and flat-gain proof inputs and the accepted separated-scales estimate. -/

namespace WangZahlLot.Obl.wz_restricted_uniform_improvement.Frostman

/-- o038 from the frozen all-scales statement. -/
theorem o038_of_A
    (hA : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.StatementA) :
    WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.O038 :=
  WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.o038_of_repairQ hA
    WangZahlLot.wz_frostman_derived_quadratic_trichotomy
    WangZahlLot.wz_separated_scales_gain WangZahlLot.wz_frostman_quadratic_flat_gain

end WangZahlLot.Obl.wz_restricted_uniform_improvement.Frostman
