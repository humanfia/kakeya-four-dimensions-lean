-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.Final.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Assembly
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfFixed

/-!
# The `s = 1/2` estimate from the rich-class step

`HalfExtractionSmall` (HalfExt/Assembly.lean) and x0505's restricted `HalfExtraction` are the
same proposition, so the rich-class step gives `FixedKatzTaoAt (1/2)` through
`half_fixed_of_extraction`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

theorem halfExtraction_of_richClass (hR : RichClassStep) : HalfExtraction :=
  halfExtractionSmall_of_richClass hR

theorem half_fixed_of_richClass (hR : RichClassStep) : FixedKatzTaoAt (1 / 2) :=
  half_fixed_of_extraction (halfExtraction_of_richClass hR)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
