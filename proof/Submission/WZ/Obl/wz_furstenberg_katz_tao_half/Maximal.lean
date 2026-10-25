-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.Maximal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Maximal subfamilies of a finite set

For a relation `R`, a finite set `D` contains a subfamily `J`, pairwise related in
both orders, which is maximal: every other element of `D` fails `R` with some
element of `J` in one of the two orders.

Ported from session x0394 (o141, commit d684c60).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

lemma exists_maximal_pairwise {α : Type*} (D : Finset α) (R : α → α → Prop) :
    ∃ J : Finset α, J ⊆ D ∧ (∀ x ∈ J, ∀ y ∈ J, x ≠ y → R x y) ∧
      ∀ q ∈ D, q ∉ J → ∃ j ∈ J, ¬ R q j ∨ ¬ R j q := by
  classical
  let Q : ℕ → Prop := fun n => ∃ J : Finset α, J ⊆ D ∧
    (∀ x ∈ J, ∀ y ∈ J, x ≠ y → R x y) ∧ J.card = n
  have hQ0 : Q 0 := ⟨∅, by simp, by simp, rfl⟩
  have hQN : ∀ n, Q n → n ≤ D.card := by
    rintro n ⟨J, hJD, _, rfl⟩
    exact Finset.card_le_card hJD
  have hQm : Q (Nat.findGreatest Q D.card) := Nat.findGreatest_spec (P := Q) (Nat.zero_le _) hQ0
  obtain ⟨J, hJD, hJpair, hJcard⟩ := hQm
  refine ⟨J, hJD, hJpair, ?_⟩
  intro q hq hqJ
  by_contra hcon
  push Not at hcon
  have hQ : Q (J.card + 1) := by
    refine ⟨insert q J, Finset.insert_subset hq hJD, ?_, Finset.card_insert_of_notMem hqJ⟩
    intro x hx y hy hxy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact (hcon y hy).1
    · exact (hcon x hx).2
    · exact hJpair x hx y hy hxy
  have := Nat.le_findGreatest (hQN _ hQ) hQ
  omega

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
