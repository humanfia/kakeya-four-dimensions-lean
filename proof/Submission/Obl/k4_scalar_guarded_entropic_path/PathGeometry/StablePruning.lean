/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/StablePruning.lean.
Its original attribution comments are retained below.
-/
import Mathlib

/-! Adapted from the same LOT tree, obligation o092, session x0317,
commit fa47b815587fe8f4cb7c4fb2eef3709b5acf849f,
Submission/Obl/k4_scalar_tangent_isotropic_improvement/SimultaneousPruning.lean.
The accepted-library search had no stable simultaneous overlap-cell pruner. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Charge each removed cell once, even for overlapping families. Every
surviving cell satisfies its floor in the FINAL selected law. -/
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
  · exact ⟨A, hA, Subset.rfl, le_add_right le_rfl, fun i hi => Or.inr (hall i hi)⟩
  push Not at hall
  obtain ⟨i, hi, hlight⟩ := hall
  obtain ⟨E, hE, hsub, hmass, hfloor⟩ := ih (S.erase i) (Finset.erase_ssubset hi)
    (fun j hj => hCells j (Finset.mem_erase.mp hj).2) (A \ Cells i) (hA.diff (hCells i hi))
  refine ⟨E, hE, hsub.trans sdiff_subset, ?_, ?_⟩
  · have hcover : A ⊆ (A \ Cells i) ∪ (A ∩ Cells i) := by
      intro a ha
      by_cases hi : a ∈ Cells i
      · exact Or.inr ⟨ha, hi⟩
      · exact Or.inl ⟨ha, hi⟩
    calc
      μ A ≤ μ (A \ Cells i) + μ (A ∩ Cells i) :=
        (measure_mono hcover).trans (measure_union_le _ _)
      _ ≤ (μ E + ∑ j ∈ S.erase i, τ j) + τ i := add_le_add hmass hlight.le
      _ = μ E + ∑ j ∈ S, τ j := by rw [add_assoc, Finset.sum_erase_add _ _ hi]
  · intro j hj
    by_cases hji : j = i
    · subst j
      left
      apply Subset.antisymm ?_ (empty_subset _)
      intro a ha
      exact False.elim ((hsub ha.1).2 ha.2)
    · exact hfloor j (Finset.mem_erase.mpr ⟨hji, hj⟩)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning
