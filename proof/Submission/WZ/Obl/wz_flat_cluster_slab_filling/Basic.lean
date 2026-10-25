-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_cluster_slab_filling.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_off_stem_brush_overlap.Counts
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularShading
import Submission.WZ.Obl.wz_finite_shading_second_moment
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.OrthogonalBox

/-!
Basic notation for the proof of `WangZahlLot.wz_flat_cluster_slab_filling`
(WZ Lemma 7.14, Steps 2-3).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_flat_cluster_slab_filling

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- The `δ`-tube around the unit segment `[x, x+v]`. -/
abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  thickening δ (segment ℝ x (x + v))

/-- The unoriented angle between two directions. -/
abbrev angle (v w : Space) : ℝ := min ‖v - w‖ ‖v + w‖

/-- The slab `{p | |⟪u,p⟫ - t| ≤ r}`. -/
abbrev Slab (u : Space) (t r : ℝ) : Set Space := {p | |inner ℝ u p - t| ≤ r}

/-- The frozen box `P a b c z e` with `ι = fun p i => p i`. -/
abbrev Box (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Set Space :=
  {p | |(e (p - z)) 0| ≤ a / 2 ∧ |(e (p - z)) 1| ≤ b / 2 ∧ |(e (p - z)) 2| ≤ c / 2}

end WangZahlLot.Obl.wz_flat_cluster_slab_filling

end
