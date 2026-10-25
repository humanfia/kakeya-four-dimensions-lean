import Mathlib

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory

noncomputable section

/-- Disjoint measurable projected pieces admit an actual measurable
label map, with a fixed fallback outside their union. -/
theorem exists_measurable_finite_label {α I : Type*} [MeasurableSpace α] [Fintype I]
    (E : I → Set α) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) (fallback : I) :
    ∃ lab : α → I, (∀ i, MeasurableSet (lab ⁻¹' {i})) ∧
      (∀ i l, l ∈ E i → lab l = i) ∧
      (∀ l, (¬ ∃ i, l ∈ E i) → lab l = fallback) := by
  classical
  let lab : α → I := fun l => if h : ∃ i, l ∈ E i then Classical.choose h else fallback
  have hmem : ∀ l, (∃ i, l ∈ E i) → l ∈ E (lab l) := by
    intro l hl
    simpa [lab, dif_pos hl] using Classical.choose_spec hl
  have heq : ∀ i l, l ∈ E i → lab l = i := by
    intro i l hl
    by_contra hne
    have hother := hmem l ⟨i, hl⟩
    exact Set.disjoint_left.mp (hdisj (lab l) i hne) hother hl
  have hdefault : ∀ l, (¬ ∃ i, l ∈ E i) → lab l = fallback := by
    intro l hl
    simp [lab, hl]
  refine ⟨lab, ?_, heq, hdefault⟩
  intro i
  by_cases hi : i = fallback
  · subst i
    have hpre : lab ⁻¹' {fallback} = E fallback ∪ (⋃ j, E j)ᶜ := by
      ext l
      constructor
      · intro hl
        by_cases he : ∃ j, l ∈ E j
        · left
          have hf : lab l = fallback := hl
          simpa [hf] using hmem l he
        · right
          simpa only [mem_compl_iff, mem_iUnion] using he
      · rintro (hl | hl)
        · exact heq fallback l hl
        · apply hdefault l
          simpa only [mem_compl_iff, mem_iUnion] using hl
    rw [hpre]
    exact (hE fallback).union (MeasurableSet.iUnion hE).compl
  · have hpre : lab ⁻¹' {i} = E i := by
      ext l
      constructor
      · intro hl
        have hf : lab l = i := hl
        by_cases he : ∃ j, l ∈ E j
        · simpa [hf] using hmem l he
        · exact (hi (hf.symm.trans (hdefault l he))).elim
      · intro hl
        exact heq i l hl
    rw [hpre]
    exact hE i

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
