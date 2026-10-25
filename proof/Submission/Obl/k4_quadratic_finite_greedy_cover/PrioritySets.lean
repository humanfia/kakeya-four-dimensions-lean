-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/PrioritySets.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.EligibilityFormat

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open Set MeasureTheory

theorem selectedUnion_insert {X ι β : Type*} [DecidableEq ι]
    (S : Finset ι) (parent : ι → β) (A : ι → Set X) (a : ι) (b : β) :
    selectedUnion (insert a S) parent A b =
      {x | parent a = b ∧ x ∈ A a} ∪ selectedUnion S parent A b := by
  ext x
  simp only [selectedUnion, mem_iUnion, Finset.mem_insert, mem_union, mem_ofPred_eq]
  aesop

theorem selectedUnion_measurable {X ι β : Type*} [MeasurableSpace X]
    (S : Finset ι) (parent : ι → β) (A : ι → Set X)
    (hAm : ∀ a ∈ S, MeasurableSet (A a)) (b : β) :
    MeasurableSet (selectedUnion S parent A b) := by
  classical
  apply Finset.measurableSet_biUnion
  intro a ha
  by_cases hab : parent a = b
  · simpa [hab] using hAm a ha
  · simp [hab]

/-- Assign all newly eligible trajectories after deleting earlier assignments.
The union still equals the union of the full eligibility envelopes. -/
theorem priority_union_insert {X ι β : Type*} [DecidableEq ι]
    (S : Finset ι) (parent : ι → β) (A E : ι → Set X) (a : ι)
    (hunion : ∀ b, selectedUnion S parent A b = selectedUnion S parent E b)
    (hnew : A a = E a \ selectedUnion S parent A (parent a)) :
    ∀ b, selectedUnion (insert a S) parent A b = selectedUnion (insert a S) parent E b := by
  intro b
  rw [selectedUnion_insert, selectedUnion_insert, hunion b]
  by_cases hab : parent a = b
  · have hnew' := hnew
    rw [hunion (parent a), hab] at hnew'
    rw [hnew']
    ext x
    simp only [mem_union, mem_ofPred_eq, hab, true_and, mem_sdiff]
    tauto
  · ext x
    simp [hab]

/-- Priority deletion makes the new assignment disjoint from every earlier
assignment with the same old packet. -/
theorem priority_disjoint_insert {X ι β : Type*} [DecidableEq ι]
    (S : Finset ι) (parent : ι → β) (A E : ι → Set X) (a : ι)
    (hdisj : ∀ b ∈ S, ∀ c ∈ S, b ≠ c → parent b = parent c → Disjoint (A b) (A c))
    (hnew : A a = E a \ selectedUnion S parent A (parent a)) :
    ∀ b ∈ insert a S, ∀ c ∈ insert a S,
      b ≠ c → parent b = parent c → Disjoint (A b) (A c) := by
  have hnewdisj (b : ι) (hb : b ∈ S) (hp : parent a = parent b) : Disjoint (A a) (A b) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    rw [hnew] at hx
    exact hx.2 (mem_iUnion₂.mpr ⟨b, hb, hp.symm, hx'⟩)
  intro b hb c hc hne hparent
  rcases Finset.mem_insert.mp hb with hba | hbs
  · subst b
    rcases Finset.mem_insert.mp hc with hca | hcs
    · exact (hne hca.symm).elim
    · exact hnewdisj c hcs hparent
  · rcases Finset.mem_insert.mp hc with hca | hcs
    · subst c
      exact (hnewdisj b hbs hparent.symm).symm
    · exact hdisj b hbs c hcs hne hparent

/-- Full eligibility remains available after priority deletion. -/
theorem priority_subset_insert {X ι β : Type*} [DecidableEq ι]
    (S : Finset ι) (parent : ι → β) (A E : ι → Set X) (a : ι)
    (hsub : ∀ b ∈ S, A b ⊆ E b)
    (hnew : A a = E a \ selectedUnion S parent A (parent a)) :
    ∀ b ∈ insert a S, A b ⊆ E b := by
  intro b hb
  rcases Finset.mem_insert.mp hb with hba | hbs
  · subst b
    rw [hnew]
    exact sdiff_subset
  · exact hsub b hbs

end Submission.Obl.k4_quadratic_finite_greedy_cover
