-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.OneLeaf.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TwoLeaves
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.PremiseLeaf

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- All profile, regularization and energy steps of the high range are
complete. The remaining input is the geometric Case A contradiction. -/
theorem high_range_of_caseA {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hA : CaseALeaf s) : FixedKatzTaoAt s :=
  high_range_of_premise_caseA hs0 hs1 (premiseLeaf hs0.le hs1) hA

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
