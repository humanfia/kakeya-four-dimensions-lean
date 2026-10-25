/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/SimultaneousPruning.lean -/
import Mathlib

/-! Stable cell-mass floors on a finite family of scales, with original measure budgets. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

/-- Remove light cells until every surviving participating cell has its floor.
The cost is charged once per removed cell, even when the cells overlap. Thus
later deletions cannot invalidate an earlier floor in the final set. -/
theorem simultaneous_cell_pruning {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Cells : ι → Set Ω) (τ : ι → ℝ≥0∞) (S : Finset ι)
    (hCells : ∀ i ∈ S, MeasurableSet (Cells i)) (A : Set Ω) (hA : MeasurableSet A) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ A ∧
      μ A ≤ μ E + (∑ i ∈ S, τ i) ∧
      ∀ i ∈ S, E ∩ Cells i = ∅ ∨ τ i ≤ μ (E ∩ Cells i) := by
  classical
  revert hCells A
  refine Finset.strongInductionOn S ?_
  intro S ih hCells A hA
  by_cases hall : ∀ i ∈ S, τ i ≤ μ (A ∩ Cells i)
  · exact ⟨A, hA, Set.Subset.rfl, le_add_right le_rfl, fun i hi => Or.inr (hall i hi)⟩
  push Not at hall
  obtain ⟨i, hi, hlight⟩ := hall
  obtain ⟨E, hE, hsub, hmass, hfloor⟩ := ih (S.erase i) (Finset.erase_ssubset hi)
    (fun j hj => hCells j (Finset.mem_erase.mp hj).2) (A \ Cells i) (hA.diff (hCells i hi))
  refine ⟨E, hE, hsub.trans Set.sdiff_subset, ?_, ?_⟩
  · have hcover : A ⊆ (A \ Cells i) ∪ (A ∩ Cells i) := by
      intro ω hω
      by_cases hmem : ω ∈ Cells i
      · exact Or.inr ⟨hω, hmem⟩
      · exact Or.inl ⟨hω, hmem⟩
    calc
      μ A ≤ μ (A \ Cells i) + μ (A ∩ Cells i) :=
        (measure_mono hcover).trans (measure_union_le _ _)
      _ ≤ (μ E + ∑ j ∈ S.erase i, τ j) + τ i := add_le_add hmass hlight.le
      _ = μ E + (∑ j ∈ S, τ j) := by rw [add_assoc, Finset.sum_erase_add _ _ hi]
  · intro j hj
    by_cases hji : j = i
    · subst j
      left
      apply Set.Subset.antisymm ?_ (Set.empty_subset _)
      intro ω hω
      exact False.elim ((hsub hω.1).2 hω.2)
    · exact hfloor j (Finset.mem_erase.mpr ⟨hji, hj⟩)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
