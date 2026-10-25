-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfFixed.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.FromHalf
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfEndgame

/-!
# The fixed-exponent estimate at `s = 1/2` from the extraction

`FixedKatzTaoAt (1/2)` (x0539's `FromHalf`) is exactly the output of `half_core`; with
`half_endgame` proved, only `HalfExtraction` remains.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

theorem half_fixed_of_extraction (hE : HalfExtraction) : FixedKatzTaoAt (1 / 2) :=
  half_core_of_extraction hE

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
