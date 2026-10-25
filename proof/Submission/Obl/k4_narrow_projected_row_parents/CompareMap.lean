import Submission.Obl.k4_narrow_projected_row_parents.ListsOfCompared

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set
open Submission.Obl.k4_general_parent_projected_layers

variable {α : Type} [MeasurableSpace α]

/-- Collapse refined projected assignments back to their original labels.
Taking images of the partner lists does not increase their size. -/
noncomputable def Compared.map_projected {a : PreparedModel α} {k : ℕ} {s : ℝ}
    {n n' : ℕ} {C : Fin n → Set α} {C' : Fin n' → Set α}
    {q χ g m M : ℝ} (cmp : Compared a k s C' q χ g m M)
    (toOld : Fin n' → Fin n) (hC : ∀ i, C' i ⊆ C (toOld i)) :
    Compared a k s C q χ g m M := by
  classical
  exact {
    R := cmp.R
    measurable_R := cmp.measurable_R
    mass := cmp.mass
    lab := fun l => toOld (cmp.lab l)
    lab_mem := fun z hz => hC _ (cmp.lab_mem z hz)
    tru := cmp.tru
    tru_mem := cmp.tru_mem
    partners := fun Q c => (cmp.partners Q c).image toOld
    partners_card := fun Q c => (Nat.cast_le.mpr Finset.card_image_le).trans (cmp.partners_card Q c)
    partners_mem := fun z hz => Finset.mem_image.mpr ⟨_, cmp.partners_mem z hz, rfl⟩ }

end Submission.Obl.k4_narrow_projected_row_parents
