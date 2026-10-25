/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/RowParents.lean.
   Earlier provenance comments in the source are retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.RowParent
import Submission.Obl.k4_narrow_projected_row_parents.ModelBridge

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter

def RowParents {α : Type} [MeasurableSpace α] (cfg : Model α) (r : ℝ) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∃ M : ℕ → ℝ, (∀ k, 1 ≤ M k) ∧ Model.Subpow cfg.N M ∧
    ∃ᶠ k in atTop, Nonempty
      (RowParent (Model.parameters cfg) (Model.prepared cfg) k r
        (cfg.N k ^ (-e)) (M k))

end Submission.Obl.k4_narrow_projected_row_parents
