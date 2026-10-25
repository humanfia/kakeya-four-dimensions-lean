-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027.Main.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.Stmts
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.G027.Glue

/- Adapted from the internal o015/x0589 assembly at effb3d2,
   WangZahlLot/Obl/wz_frostman_all_scales_volume/G027/Main.lean; original session credits below are retained. -/

/-!
The glue of o027's split (session x0081): sticky twisted extraction from accepted o060, o061,
o063 and the C2 regularization of grains (taken as a hypothesis).
-/

theorem WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027.main_of (h062 : WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.Stmts.O062) :
    WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.Stmts.O027 := by
  exact WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.G027.extraction_of_children h062
