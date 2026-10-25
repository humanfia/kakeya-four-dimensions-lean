-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.WholeBlockFailurePruning, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped ENNReal BigOperators

/-- Remove whole bad blocks. On every surviving block the source is
EXACTLY unchanged and its failure ratio is small. The loss is charged
to the total failure mass, with no block-count factor. -/
theorem exists_whole_block_small_failure_source {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E bad : Set Ω) (hE : MeasurableSet E) (hbad : MeasurableSet bad)
    (blocks : I → Set Ω) (indices : Finset I)
    (hblocks : ∀ i∈indices, MeasurableSet (blocks i))
    (hdisjoint : ∀ i∈indices, ∀ j∈indices, i≠j → Disjoint (E∩blocks i) (E∩blocks j))
    (ratio : ENNReal) (hratio0 : ratio≠0) (hratioTop : ratio≠∞) :
    ∃ keep : Set Ω, MeasurableSet keep ∧ keep⊆E ∧
      μ (E\keep)≤ratio⁻¹*μ (E∩bad) ∧
      ∀ i∈indices, keep∩blocks i=∅ ∨
        keep∩blocks i=E∩blocks i ∧ μ ((keep∩blocks i)∩bad)≤ratio*μ (keep∩blocks i) := by
  classical
  let deleted := indices.filter (fun i => ¬μ ((E∩blocks i)∩bad)≤ratio*μ (E∩blocks i))
  let removed := ⋃ i∈deleted, blocks i
  let keep := E\removed
  have hdel (i : I) (hi : i∈deleted) : i∈indices ∧
      ¬μ ((E∩blocks i)∩bad)≤ratio*μ (E∩blocks i) := Finset.mem_filter.mp hi
  have hremoved : MeasurableSet removed :=
    Finset.measurableSet_biUnion deleted (fun i hi => hblocks i (hdel i hi).1)
  have hkeep : MeasurableSet keep := hE.diff hremoved
  have hpiece (i : I) (hi : i∈deleted) : μ (E∩blocks i)≤ratio⁻¹*μ ((E∩blocks i)∩bad) := by
    have hbound : ratio*μ (E∩blocks i)≤μ ((E∩blocks i)∩bad) := (lt_of_not_ge (hdel i hi).2).le
    calc
      _ = ratio⁻¹*(ratio*μ (E∩blocks i)) := by
        rw [←mul_assoc,ENNReal.inv_mul_cancel hratio0 hratioTop,one_mul]
      _ ≤ _ := mul_le_mul' le_rfl hbound
  have hsum : (∑ i∈deleted, μ ((E∩blocks i)∩bad))≤μ (E∩bad) := by
    have hd : (deleted : Set I).Pairwise
        (Function.onFun (AEDisjoint μ) (fun i => (E∩blocks i)∩bad)) := by
      intro i hi j hj hij
      exact (hdisjoint i (hdel i hi).1 j (hdel j hj).1 hij).mono
        inter_subset_left inter_subset_left |>.aedisjoint
    rw [←measure_biUnion_finset₀ hd (fun i hi => ((hE.inter (hblocks i (hdel i hi).1)).inter hbad).nullMeasurableSet)]
    exact measure_mono (iUnion₂_subset (fun i _ z hz => ⟨hz.1.1,hz.2⟩))
  refine ⟨keep,hkeep,sdiff_subset,?_,?_⟩
  · calc
      μ (E\keep)≤μ (⋃ i∈deleted, E∩blocks i) := by
        apply measure_mono
        intro z hz
        have hr : z∈removed := by
          by_contra hn
          exact hz.2 ⟨hz.1,hn⟩
        obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hr
        exact mem_iUnion₂.mpr ⟨i,hi,hz.1,hzi⟩
      _ ≤ ∑ i∈deleted, μ (E∩blocks i) := measure_biUnion_finset_le _ _
      _ ≤ ∑ i∈deleted, ratio⁻¹*μ ((E∩blocks i)∩bad) := Finset.sum_le_sum hpiece
      _ = ratio⁻¹*(∑ i∈deleted, μ ((E∩blocks i)∩bad)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul' le_rfl hsum
  · intro i hi
    by_cases hratio : μ ((E∩blocks i)∩bad)≤ratio*μ (E∩blocks i)
    · right
      have heq : keep∩blocks i=E∩blocks i := by
        ext z
        constructor
        · exact fun hz => ⟨hz.1.1,hz.2⟩
        · rintro ⟨hzE,hzi⟩
          refine ⟨⟨hzE,?_⟩,hzi⟩
          intro hr
          obtain ⟨j,hj,hzj⟩ := mem_iUnion₂.mp hr
          have hji : i≠j := by
            intro hij
            subst j
            exact (hdel i hj).2 hratio
          exact (disjoint_left.mp (hdisjoint i hi j (hdel j hj).1 hji)) ⟨hzE,hzi⟩ ⟨hzE,hzj⟩
      exact ⟨heq,by simpa only [heq] using hratio⟩
    · left
      have hid : i∈deleted := Finset.mem_filter.mpr ⟨hi,hratio⟩
      apply eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz,hzi⟩
      exact hz.2 (mem_iUnion₂.mpr ⟨i,hid,hzi⟩)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
