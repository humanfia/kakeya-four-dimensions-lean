/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/WeightedPartitionFloors.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.SimultaneousPruning

/-! Stable partition floors with exact original palette weights. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem simultaneous_weighted_partition_floors {Ω I C : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (hAfin : μ A ≠ ∞)
    (code : I → Ω → C) (hcode : ∀ i c, MeasurableSet {p | code i p = c})
    (hfinite : ∀ i, (code i '' A).Finite) (τ : I → C → ℝ≥0∞) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ A ∧
      μ (A \ E) ≤ ∑ i : I, ∑ c ∈ (hfinite i).toFinset, τ i c ∧
      ∀ i p, p ∈ E → τ i (code i p) ≤ μ (E ∩ {p' | code i p' = code i p}) := by
  classical
  let D : I → Finset C := fun i => (hfinite i).toFinset
  let S : Finset (Σ _ : I, C) := Finset.univ.sigma D
  let Cells : (Σ _ : I, C) → Set Ω := fun ic => {p | code ic.1 p = ic.2}
  obtain ⟨E,hE,hsub,hmass,hfloor⟩ := simultaneous_cell_pruning μ Cells
    (fun ic => τ ic.1 ic.2) S (fun ic _ => hcode ic.1 ic.2) A hA
  refine ⟨E,hE,hsub,?_,?_⟩
  · have hEfin : μ E ≠ ∞ := ne_top_of_le_ne_top hAfin (measure_mono hsub)
    apply ENNReal.le_of_add_le_add_right hEfin
    calc
      _ = μ A := by
        have h := measure_sdiff_add_inter A hE (μ := μ)
        rwa [Set.inter_eq_right.mpr hsub] at h
      _ ≤ μ E + ∑ ic ∈ S, τ ic.1 ic.2 := hmass
      _ = _ := by rw [Finset.sum_sigma]; exact add_comm _ _
  · intro i p hp
    have hmem : (⟨i,code i p⟩ : Σ _ : I, C) ∈ S :=
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, (hfinite i).mem_toFinset.mpr ⟨p,hsub hp,rfl⟩⟩
    rcases hfloor _ hmem with hempty | hf
    · exfalso
      have h : p ∈ E ∩ Cells ⟨i,code i p⟩ := ⟨hp,rfl⟩
      simp [hempty] at h
    · exact hf

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
