import Mathlib

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Set MeasureTheory
open scoped BigOperators

/-- Assign a trajectory to the first fitting member of an ordered family. -/
def firstAssignment {α : Type*} {C : ℕ} (S : Fin C → Set α) (i : Fin C) : Set α :=
  {x | x ∈ S i ∧ ∀ j, j < i → x ∉ S j}

/-- Priority assignments are pairwise disjoint, even when the original fits overlap. -/
theorem firstAssignment_disjoint {α : Type*} {C : ℕ} (S : Fin C → Set α) :
    Pairwise (fun i j => Disjoint (firstAssignment S i) (firstAssignment S j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with h | h
  · exact hy.2 i h hx.1
  · exact hx.2 j h hy.1

/-- Priority assignment retains the full union of the original candidates. -/
theorem iUnion_firstAssignment {α : Type*} {C : ℕ} (S : Fin C → Set α) :
    (⋃ i, firstAssignment S i) = ⋃ i, S i := by
  classical
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hi.1⟩
  · rintro ⟨i, hi⟩
    have hex : ∃ n : ℕ, ∃ j : Fin C, j.val = n ∧ x ∈ S j := ⟨i, i, rfl, hi⟩
    obtain ⟨j, hjn, hj⟩ := Nat.find_spec hex
    refine ⟨j, hj, ?_⟩
    intro k hkj hk
    have hminimal := Nat.find_min' hex ⟨k, rfl, hk⟩
    have hlt : k.val < j.val := hkj
    omega

/-- Priority assignment only adds finite Boolean operations and remains measurable. -/
theorem measurableSet_firstAssignment {α : Type*} [MeasurableSpace α] {C : ℕ}
    (S : Fin C → Set α) (hS : ∀ i, MeasurableSet (S i)) (i : Fin C) :
    MeasurableSet (firstAssignment S i) := by
  have heq : firstAssignment S i = S i ∩ ⋂ j ∈ {j : Fin C | j < i}, (S j)ᶜ := by
    ext x
    simp only [firstAssignment, mem_ofPred_eq, mem_inter_iff, mem_iInter,
      mem_compl_iff]
  rw [heq]
  exact (hS i).inter (MeasurableSet.biInter (Set.to_countable _) (fun j _ => (hS j).compl))

/-- The first-fit assignment for a list is the current fit with all earlier
list entries removed; this identifies its original unnormalized mass. -/
theorem firstAssignment_get {α β : Type*} (F : β → Set α) (l : List β)
    (i : Fin l.length) :
    firstAssignment (fun j : Fin l.length => F (l.get j)) i =
      F (l.get i) \ ⋃ b ∈ l.take i.val, F b := by
  ext x
  simp only [firstAssignment, mem_ofPred_eq, mem_sdiff, mem_iUnion, not_exists]
  apply and_congr_right
  intro hx
  constructor
  · intro h b hb
    obtain ⟨j, hj, hjb⟩ := List.mem_take_iff_getElem.mp hb
    let j' : Fin l.length := ⟨j, (lt_min_iff.mp hj).2⟩
    have hji : j' < i := (lt_min_iff.mp hj).1
    simpa only [j', List.get_eq_getElem, hjb] using h j' hji
  · intro h j hj
    apply h (l.get j)
    apply List.mem_take_iff_getElem.mpr
    exact ⟨j.val, lt_min (show j.val < i.val from hj) j.isLt, List.get_eq_getElem.symm⟩

end Submission.Lib.K4FinitePlankAtlases
