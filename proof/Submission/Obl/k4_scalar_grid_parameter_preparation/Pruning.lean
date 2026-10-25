/- Adapted from this LOT tree, o078, session x0260, commit 34c7136a25cd.
   Original file: Submission/Lib/K4ExactMeasureTools/Pruning.lean -/
/- Original-weight scalar measure and velocity-graph support.
Adapted from: here:o078
-/

import Mathlib

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open MeasureTheory Set
open scoped ENNReal

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- Simultaneous restoration of current floors. A maximal collection of
deleted entries replaces an iterative peeling algorithm, and charges each
entry at most once even when the entries overlap. -/
theorem exists_floor_pruning (μ : Measure α) (C : ι → Set α) (b : ι → ℝ≥0∞) :
    ∃ J : Finset ι,
      μ (⋃ i ∈ J, C i) ≤ ∑ i ∈ J, b i ∧
      ∀ i, i ∈ J ∨ b i < μ (C i \ ⋃ j ∈ J, C j) := by
  classical
  let candidates : Finset (Finset ι) := Finset.univ.powerset.filter
    (fun J => μ (⋃ i ∈ J, C i) ≤ ∑ i ∈ J, b i)
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨J, hJ, hmax⟩ := candidates.exists_max_image Finset.card hnonempty
  have hcost : μ (⋃ i ∈ J, C i) ≤ ∑ i ∈ J, b i := (Finset.mem_filter.mp hJ).2
  refine ⟨J, hcost, ?_⟩
  intro i
  by_cases hi : i ∈ J
  · exact Or.inl hi
  · right
    by_contra hbad
    have hsmall : μ (C i \ ⋃ j ∈ J, C j) ≤ b i := le_of_not_gt hbad
    have hunion : (⋃ j ∈ insert i J, C j) =
        (⋃ j ∈ J, C j) ∪ (C i \ ⋃ j ∈ J, C j) := by
      ext x
      simp only [mem_iUnion, Finset.mem_insert, mem_union, mem_sdiff]
      constructor
      · rintro ⟨a, ha, hax⟩
        rcases ha with rfl | ha
        · by_cases hx : ∃ a, ∃ _ : a ∈ J, x ∈ C a
          · exact Or.inl hx
          · exact Or.inr ⟨hax, hx⟩
        · exact Or.inl ⟨a, ha, hax⟩
      · rintro (⟨a, ha, hax⟩ | ⟨hx, _⟩)
        · exact ⟨a, Or.inr ha, hax⟩
        · exact ⟨i, Or.inl rfl, hx⟩
    have hinsert : insert i J ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset,
        Finset.subset_univ, true_and]
      calc
        μ (⋃ j ∈ insert i J, C j) ≤
            μ (⋃ j ∈ J, C j) + μ (C i \ ⋃ j ∈ J, C j) := by
          rw [hunion]
          exact measure_union_le _ _
        _ ≤ (∑ j ∈ J, b j) + b i := add_le_add hcost hsmall
        _ = ∑ j ∈ insert i J, b j := by rw [Finset.sum_insert hi, add_comm]
    have hcard := hmax _ hinsert
    rw [Finset.card_insert_of_notMem hi] at hcard
    omega

/-- The retained measurable event simultaneously has every prescribed floor
or zero mass, with a single total deletion budget. -/
theorem exists_measurable_floor_pruning (μ : Measure α)
    (C : ι → Set α) (b : ι → ℝ≥0∞) (hC : ∀ i, MeasurableSet (C i))
    {E : Set α} (hE : MeasurableSet E) :
    ∃ R : Set α, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ ∑ i, b i ∧
      ∀ i, μ (R ∩ C i) = 0 ∨ b i ≤ μ (R ∩ C i) := by
  classical
  obtain ⟨J, hcost, hfloor⟩ := exists_floor_pruning μ (fun i => E ∩ C i) b
  let U : Set α := ⋃ i ∈ J, E ∩ C i
  have hU : MeasurableSet U := by
    exact MeasurableSet.biUnion (J.finite_toSet.countable) (fun i _ => hE.inter (hC i))
  refine ⟨E \ U, hE.diff hU, sdiff_subset, ?_, ?_⟩
  · calc
      μ (E \ (E \ U)) ≤ μ U := measure_mono (by intro x hx; simp only [mem_sdiff] at hx; tauto)
      _ ≤ ∑ i ∈ J, b i := hcost
      _ ≤ ∑ i, b i := Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
  · intro i
    have heq : (E \ U) ∩ C i = (E ∩ C i) \ U := by ext x; simp only [mem_inter_iff, mem_sdiff]; tauto
    rw [heq]
    rcases hfloor i with hi | hi
    · left
      have hsub : E ∩ C i ⊆ U := by
        intro x hx
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hx⟩⟩
      rw [sdiff_eq_empty.mpr hsub, measure_empty]
    · exact Or.inr hi.le

end Submission.Obl.k4_scalar_grid_parameter_preparation
