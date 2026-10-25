-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/LiteralPartnerMenus.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib

/-! Extend the finite domain dictionaries to every literal code. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open scoped Classical

noncomputable section

def literalMenu {Q Code I : Type*} (decode : Q → Code) (menu : Q → Finset I) (c : Code) : Finset I :=
  if h : ∃ q, decode q = c then menu (Classical.choose h) else ∅

theorem literalMenu_at_decode {Q Code I : Type*} (decode : Q → Code)
    (hinj : Function.Injective decode) (menu : Q → Finset I) (q : Q) :
    literalMenu decode menu (decode q) = menu q := by
  have hex : ∃ q', decode q' = decode q := ⟨q, rfl⟩
  have heq : Classical.choose hex = q := hinj (Classical.choose_spec hex)
  simp only [literalMenu, dite_eq_left hex, heq]

theorem literalMenu_card_le {Q Code I : Type*} (decode : Q → Code) (menu : Q → Finset I)
    {B : ℝ} (hB : 0 ≤ B) (hmenu : ∀ q, ((menu q).card : ℝ) ≤ B) (c : Code) :
    ((literalMenu decode menu c).card : ℝ) ≤ B := by
  unfold literalMenu
  split_ifs with h
  · exact hmenu _
  · simpa only [Finset.card_empty, Nat.cast_zero] using hB

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
