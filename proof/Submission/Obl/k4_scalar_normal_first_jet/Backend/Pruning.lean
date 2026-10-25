/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/Pruning.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/Pruning.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_grid_parameter_preparation.Pruning

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend

open MeasureTheory Set
open scoped ENNReal

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

/-- The retained measurable event simultaneously makes each cell empty
or gives its CURRENT mass a strict floor, with one total deletion budget. -/
theorem exists_measurable_current_floor_pruning (μ : Measure α)
    (C : ι → Set α) (b : ι → ℝ≥0∞) (hC : ∀ i, MeasurableSet (C i))
    {E : Set α} (hE : MeasurableSet E) :
    ∃ R : Set α, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ ∑ i, b i ∧
      ∀ i, R ∩ C i = ∅ ∨ b i < μ (R ∩ C i) := by
  classical
  obtain ⟨J, hcost, hfloor⟩ := Submission.Obl.k4_scalar_grid_parameter_preparation.exists_floor_pruning μ (fun i => E ∩ C i) b
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
      exact sdiff_eq_empty.mpr hsub
    · exact Or.inr hi


end Submission.Obl.k4_scalar_normal_first_jet.Backend
