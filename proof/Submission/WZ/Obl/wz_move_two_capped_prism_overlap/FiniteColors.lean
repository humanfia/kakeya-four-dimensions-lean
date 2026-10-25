-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.FiniteColors.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, FiniteColors.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

/-- Color each finite fibre injectively using a common palette. Colors can
be reused in different fibres. -/
theorem finite_fiber_colors {L N m : ℕ} (hm : 0 < m)
    (A : Finset (Fin L)) (γ : Fin L → Fin N)
    (hcard : ∀ k, (A.filter fun j => γ j = k).card ≤ m) :
    ∃ color : Fin L → Fin m, ∀ i ∈ A, ∀ j ∈ A,
      γ i = γ j → color i = color j → i = j := by
  classical
  let F := fun k => A.filter fun j => γ j = k
  have hex (k : Fin N) : Nonempty (F k ↪ Fin m) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_coe, Fintype.card_fin] using hcard k
  let enc := fun k => (hex k).some
  let c : Fin N → Fin L → Fin m := fun k j =>
    if hj : j ∈ F k then enc k ⟨j, hj⟩ else ⟨0, hm⟩
  let color : Fin L → Fin m := fun j => c (γ j) j
  refine ⟨color, ?_⟩
  intro i hi j hj hγ hc
  have hmem : i ∈ F (γ j) := Finset.mem_filter.mpr ⟨hi, hγ⟩
  have hmem' : j ∈ F (γ j) := Finset.mem_filter.mpr ⟨hj, rfl⟩
  have he : c (γ j) i = c (γ j) j := by simpa only [color, hγ] using hc
  dsimp only [c] at he
  rw [dite_eq_left hmem, dite_eq_left hmem'] at he
  exact congrArg Subtype.val ((enc (γ j)).injective he)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
