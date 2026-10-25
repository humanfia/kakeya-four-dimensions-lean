-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.TwoLeaves.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0675 High/TwoLeaves.lean (b19b589).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TopLevel
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Uniformity
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.ConfigLeaf

/-!
# The high range from the premise and case A

With `configLeaf` (`High/ConfigLeaf.lean`) and `uniformityLeaf` (`High/Uniformity.lean`)
proved, `high_range_of_leaves` leaves two statements: the energy premise and case A.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- **The high range from the premise and case A.** -/
theorem high_range_of_premise_caseA {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hE : PremiseLeaf s) (hA : CaseALeaf s) : FixedKatzTaoAt s :=
  high_range_of_leaves hs0 hs1 (configLeaf hs0 hs1) hE (uniformityLeaf hs0 hs1) hA

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
