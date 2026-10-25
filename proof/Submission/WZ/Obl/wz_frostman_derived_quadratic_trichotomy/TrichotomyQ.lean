-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.TrichotomyQ.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.CompositionQ
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyQ
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.NonStickyQ

/-! The derived trichotomy from x0338's two quadratic-count branch proofs. -/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- **The derived trichotomy with the quadratic count.** -/
theorem trichotomyDerivedQ_holds : TrichotomyDerivedQ :=
  trichotomyDerivedQ_of_branches X318.stickyBranchStmtQ_holds X318.nonStickyBranchStmtQ_holds

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
