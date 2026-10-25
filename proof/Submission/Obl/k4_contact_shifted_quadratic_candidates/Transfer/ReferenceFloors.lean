/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/ReferenceFloors.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic.Linarith

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set
open scoped BigOperators

/-- Simultaneous final mass floors for an arbitrary finite family of events.
The events may overlap, as do the label events at different depths. Each
original reference weight is charged once. -/
theorem exists_simultaneous_reference_floors {Ω I : Type*} [MeasurableSpace Ω]
    [DecidableEq I] (μ : Measure Ω) [IsFiniteMeasure μ]
    (G : Set Ω) (hG : MeasurableSet G) (E : I → Set Ω) (F : Finset I)
    (hE : ∀ i ∈ F, MeasurableSet (E i)) (w : I → ℝ) (hw : ∀ i ∈ F, 0 ≤ w i) :
    ∃ (S : Finset I) (G' : Set Ω), S ⊆ F ∧ MeasurableSet G' ∧ G' ⊆ G ∧
      (∀ p ∈ G', ∀ i ∈ F, p ∈ E i → i ∈ S) ∧
      (∀ i ∈ S, w i ≤ (μ.restrict G').real (E i)) ∧
      μ.real G ≤ μ.real G' + ∑ i ∈ F, w i := by
  classical
  let keep (S : Finset I) : Set Ω := G \ ⋃ i ∈ F \ S, E i
  have hkeep (S : Finset I) : MeasurableSet (keep S) :=
    hG.diff (MeasurableSet.biUnion (F \ S).countable_toSet
      (fun i hi => hE i (Finset.mem_sdiff.mp hi).1))
  have hmem (S : Finset I) (p : Ω) :
      p ∈ keep S ↔ p ∈ G ∧ ∀ i ∈ F, p ∈ E i → i ∈ S := by
    constructor
    · rintro ⟨hpG, hpout⟩
      refine ⟨hpG, ?_⟩
      intro i hi hpE
      by_contra his
      exact hpout (mem_iUnion₂.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, his⟩, hpE⟩)
    · rintro ⟨hpG, hpS⟩
      refine ⟨hpG, ?_⟩
      intro hpout
      obtain ⟨i, hi, hpE⟩ := mem_iUnion₂.mp hpout
      exact (Finset.mem_sdiff.mp hi).2 (hpS i (Finset.mem_sdiff.mp hi).1 hpE)
  let objective (S : Finset I) : ℝ := μ.real (keep S) - ∑ i ∈ S, w i
  obtain ⟨S, hSF, hmax⟩ := Finset.exists_max_image F.powerset objective
    ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset F)⟩
  have hSF' : S ⊆ F := Finset.mem_powerset.mp hSF
  refine ⟨S, keep S, hSF', hkeep S, sdiff_subset, ?_, ?_, ?_⟩
  · intro p hp
    exact (hmem S p).mp hp |>.2
  · intro i hi
    have hiF : i ∈ F := hSF' hi
    have hdrop : keep (S.erase i) = keep S \ E i := by
      ext p
      rw [hmem]
      constructor
      · rintro ⟨hpG, hpS⟩
        refine ⟨(hmem S p).mpr ⟨hpG, fun j hj hpj =>
          (Finset.mem_erase.mp (hpS j hj hpj)).2⟩, ?_⟩
        intro hpi
        exact (Finset.mem_erase.mp (hpS i hiF hpi)).1 rfl
      · rintro ⟨hp, hpi⟩
        obtain ⟨hpG, hpS⟩ := (hmem S p).mp hp
        refine ⟨hpG, ?_⟩
        intro j hj hpj
        refine Finset.mem_erase.mpr ⟨?_, hpS j hj hpj⟩
        intro hji
        subst j
        exact hpi hpj
    have hpart : μ.real (keep S) =
        μ.real (keep (S.erase i)) + μ.real (keep S ∩ E i) := by
      rw [hdrop]
      have h := measureReal_inter_add_sdiff (μ := μ) (s := keep S) (hE i hiF)
      linarith
    have hmaxdrop := hmax (S.erase i)
      (Finset.mem_powerset.mpr ((Finset.erase_subset i S).trans hSF'))
    have hsum := Finset.sum_erase_add S w hi
    have hfloor : w i ≤ μ.real (keep S ∩ E i) := by
      dsimp only [objective] at hmaxdrop
      linarith
    have heq : (μ.restrict (keep S)).real (E i) = μ.real (keep S ∩ E i) := by
      simp only [measureReal_def, Measure.restrict_apply (hE i hiF), inter_comm]
    exact heq.symm ▸ hfloor
  · have hmaxall := hmax F (Finset.mem_powerset.mpr (Finset.Subset.refl F))
    have hfull : keep F = G := by simp [keep]
    have hsum : 0 ≤ ∑ i ∈ S, w i := Finset.sum_nonneg (fun i hi => hw i (hSF' hi))
    dsimp only [objective] at hmaxall
    rw [hfull] at hmaxall
    linarith

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
