/-
Adapted from: here:o266
Three-base-direction tools of session x0947 on o266 (branch x0947), moved into a library.
-/
import Submission.Lib.K4ThreeBaseRows.EntryPruning
import Submission.Lib.K4ThreeBaseRows.RowBins
import Submission.Lib.K4ThreeBaseRows.SupportedTriples
import Submission.Lib.K4ThreeBaseRows.CartesianField3

/-!
# Three-base-direction row lists, entry pruning and Cartesian fields

Tools for the velocity-graph and field steps of the paper's §6 (`tex-06-isotropic.tex`) with THREE
base coordinates `(t, y₀, y₁)` and lifted base directions `(1, V₀, V₁)`.

- `EntryPruning` (`Full7EntryPruning`): full7 coefficient blocks use at most `cellConst K / p`
  manufactured physical cells. Reference pruning against prior floors costs
  `δ · cellConst K · θ(univ)`, and `X'` lists per (physical cell, velocity code) have size
  `≤ (4K + 12) Kcap/(δζ)`.
- `RowBins` (`RowBinLists`): adjugate stability of spanning witness triples and per-tuple row-bin
  counts. Coarse row lists come in two forms: one heavy tuple per cell, or the weighted form
  (`coarse_row_bins_card_le_weighted`) with a total product palette per cell.
- `SupportedTriples`: actual representatives and Good triples from `Broad` cell laws with per-bin
  palette domination. `coarse_row_bins_card_le_of_broad`, `..._all_meshes` and `..._normalized`
  give end-to-end coarse row-bin counts.
- `CartesianField3`: the three-coordinate Cartesian polynomial field kernel
  `exists_cartesian_polynomial_fields3`. It consumes degree-`D` fits along `x`-, `y`- and
  `z`-fibers and constructs no witnesses. It generalizes the accepted 2D
  `K4ScalarCoreTools.Finalization.exists_cartesian_polynomial_fields`.
-/
