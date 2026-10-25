-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.Assembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.G015.Twisted
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.G027.Main
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.G103.Main
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.Regularization
import Submission.WZ.Obl.wz_broad_grains_improvement.StickyGain
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.FromHalf
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.OfA
import Submission.WZ.Obl.wz_twisted_projection_volume

/- The assembly follows internal o015/x0589, effb3d2, Assembly.lean.
   Its G141 and G157 chains are supplied directly by the accepted o158 and o213
   interfaces. Only the still-unaccepted composition is carried in this namespace. -/

namespace WangZahlLot.Obl.wz_broad_grains_improvement.Frostman

set_option maxHeartbeats 1200000

theorem all_scales_of_regularization (h062 : Stmts.O062) : FrostmanAllScales :=
  G015.statement_of_twisted (G027.main_of h062) WangZahlLot.wz_twisted_projection_volume

theorem all_scales_of_linearity (h103 : Stmts.O103) : FrostmanAllScales :=
  all_scales_of_regularization (regularization_of_linearity h103)

theorem all_scales_of_high (h214 : Stmts.O214) : FrostmanAllScales := by
  have h157 : Stmts.O157 :=
    WangZahlLot.Obl.wz_furstenberg_katz_tao_half.furstenberg_of_half_and_open
      WangZahlLot.wz_furstenberg_katz_tao_half h214
  have h141 : Stmts.O141 := WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.o141_of_A h157
  exact all_scales_of_linearity (G103.main_of h141)

/-- The accepted high-range Furstenberg theorem completes the all-scales volume bound. -/
theorem Assembly.all_scales : FrostmanAllScales :=
  all_scales_of_high WangZahlLot.wz_furstenberg_katz_tao_high

end WangZahlLot.Obl.wz_broad_grains_improvement.Frostman
