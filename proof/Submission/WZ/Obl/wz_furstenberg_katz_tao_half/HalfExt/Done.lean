-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.HalfExt.Done.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.RichClass
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.HalfExt.Final

/-!
# The fixed estimate at `s = 1/2`

`half_rich_class` is the rich-class step, so `half_fixed_of_richClass` gives
`FixedKatzTaoAt (1/2)` (the statement of o213 `wz_furstenberg_katz_tao_half`).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

theorem richClassStep_holds : RichClassStep :=
  fun ε₀ η h1 h2 h3 h4 => half_rich_class ε₀ η h1 h2 h3 h4

theorem half_fixed_katz_tao : FixedKatzTaoAt (1 / 2) :=
  half_fixed_of_richClass richClassStep_holds

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
