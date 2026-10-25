-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.SmallToFull.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.LargeComparison
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.SmallImprovement

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

/-- The full frozen comparison interface reduces to comparisons with exponent below `1/100`. -/
theorem full_comparison_of_small_comparisons
    (hsmall : ∀ θ : ℝ, 0 < θ → θ < 1 / 100 → ComparisonAt θ) :
    WangZahlLot.Obl.wz_normalized_projection_iteration.CoarseFine :=
  cf_of_b (projection_estimate_of_small_comparisons hsmall)

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
