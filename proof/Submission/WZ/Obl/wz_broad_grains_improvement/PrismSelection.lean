-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.PrismSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap (PrismData)

/-- A change of coarse carriers that keeps a subfamily of the original prism
centres, frames, and all its incidence pieces. The angular width may change. -/
def PrismSelection {n : ℕ} (D D' : PrismData n) : Prop :=
  D'.a = D.a ∧ ∃ τ : Fin D'.L → Fin D.L, Function.Injective τ ∧
    D'.z = D.z ∘ τ ∧ D'.e = D.e ∘ τ ∧ ∀ i, D'.W i = D.W i ∘ τ

end WangZahlLot.Obl.wz_broad_grains_improvement
