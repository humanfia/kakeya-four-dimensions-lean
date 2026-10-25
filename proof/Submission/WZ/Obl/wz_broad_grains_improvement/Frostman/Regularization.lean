-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.Frostman.Regularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.Stmts
import Submission.WZ.Obl.wz_slab_local_linearity
import Submission.WZ.Obl.wz_multiscale_c2_extraction
import Submission.WZ.Obl.wz_c2_slope_normalization
import Submission.WZ.Obl.wz_c2_slope_normalization.BoundedSlope

/- The composition follows the internal o015/x0589 assembly at effb3d2,
   G062/Main.lean and G062/Glue.lean. The bounded-slope argument and separated-cover
   conversions are imported from accepted o106 rather than reproduced. -/

namespace WangZahlLot.Obl.wz_broad_grains_improvement.Frostman

open WangZahlLot.Obl.wz_c2_slope_normalization

set_option maxHeartbeats 1200000

theorem regularization_of_linearity (h103 : Stmts.O103) : Stmts.O062 := by
  intro σ hσ hσ1 hbelow habove hL
  have hbounded : LipschitzExamples σ := by
    intro η d₀ hη hd₀
    obtain ⟨δ, hδ, hδd, hδmax, n, x, v, Y, hD, hS, hC, hV, f, P, hf, hG⟩ :=
      hL η d₀ hη hd₀
    exact ⟨δ, hδ, hδd, hδmax, n, x, v, Y,
      ⟨hD, strong_of_flat hS, hC, hV⟩, f, P, hf, hG⟩
  have hlin := WangZahlLot.wz_slab_local_linearity _ rfl h103
  have hW := WangZahlLot.wz_multiscale_c2_extraction
    _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl hlin σ hσ hσ1 habove (by
      intro η d₀ hη hd₀
      obtain ⟨δ, hδ, hδd, hδmax, n, x, v, Y, ⟨hD, hS, hC, hV⟩,
        f, P, hf, hfb, hG⟩ := hbounded.bounded_slope η d₀ hη hd₀
      exact ⟨δ, hδ, hδd, hδmax, n, x, v, Y,
        hD, flat_of_strong hS, hC, hV, f, P, ⟨hf, hfb⟩, hG⟩)
  exact WangZahlLot.wz_c2_slope_normalization
    _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl σ hσ hσ1 hbelow habove hW

end WangZahlLot.Obl.wz_broad_grains_improvement.Frostman
