-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G103.Main.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.Stmts
import Submission.WZ.Obl.wz_kaufman_projection_count
import Submission.WZ.Obl.wz_nonconcentrated_dot_products
import Submission.WZ.Obl.wz_separated_projection_dichotomy
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated

/- Adapted from the internal o015/x0589 assembly at effb3d2,
   WangZahlLot/Obl/wz_frostman_all_scales_volume/G103/Main.lean; original session credits below are retained. -/

/-!
The glue of o103's split (session x0289): sticky Theorem 5.2 from the accepted Section 8
children and the OSW bootstrap (taken as a hypothesis).
-/

theorem WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G103.main_of (h141 : WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.Stmts.O141) :
    WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.Stmts.O103 :=
  WangZahlLot.wz_ad_dichotomy_from_separated
    (WangZahlLot.wz_separated_projection_dichotomy WangZahlLot.wz_kaufman_projection_count
      (WangZahlLot.wz_nonconcentrated_dot_products WangZahlLot.wz_kaufman_projection_count
        h141))
