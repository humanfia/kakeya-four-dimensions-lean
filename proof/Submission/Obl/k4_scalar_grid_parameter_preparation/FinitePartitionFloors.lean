/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/FinitePartitionFloors.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.SimultaneousPruning

/-! Stable mass floors for finitely many partitions, charged against support counts. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem simultaneous_finite_partition_floors {Ω I C : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (hAfin : μ A ≠ ∞)
    (code : I → Ω → C) (hcode : ∀ i c, MeasurableSet {p | code i p = c})
    (hfinite : ∀ i, (code i '' A).Finite) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L B : ℝ) (hL : 0 ≤ L) (hB : 0 < B)
    (hcount : ∀ i, ((code i '' A).ncard : ℝ) * w i ≤ L) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ A ∧
      μ (A \ E) ≤ ENNReal.ofReal ((Fintype.card I : ℝ) * L / B) ∧
      ∀ i p, p ∈ E → ENNReal.ofReal (w i / B) ≤ μ (E ∩ {p' | code i p' = code i p}) := by
  classical
  let D : I → Finset C := fun i => (hfinite i).toFinset
  let S : Finset (Σ _ : I, C) := Finset.univ.sigma D
  let Cells : (Σ _ : I, C) → Set Ω := fun ic => {p | code ic.1 p = ic.2}
  let τ : (Σ _ : I, C) → ℝ≥0∞ := fun ic => ENNReal.ofReal (w ic.1 / B)
  obtain ⟨E, hE, hsub, hmass, hfloor⟩ := simultaneous_cell_pruning μ Cells τ S
    (fun ic _ => hcode ic.1 ic.2) A hA
  have hsum : (∑ ic ∈ S, τ ic) ≤ ENNReal.ofReal ((Fintype.card I : ℝ) * L / B) := by
    have hinner (i : I) : (∑ c ∈ D i, ENNReal.ofReal (w i / B)) ≤ ENNReal.ofReal (L / B) := by
      have hD : ((D i).card : ℝ) * w i ≤ L := by
        rw [← Set.ncard_eq_toFinset_card _ (hfinite i)]
        exact hcount i
      calc
        _ = ENNReal.ofReal (((D i).card : ℝ) * w i / B) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          ring
        _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hD hB.le)
    calc
      _ = ∑ i : I, ∑ c ∈ D i, ENNReal.ofReal (w i / B) := Finset.sum_sigma _ _ _
      _ ≤ ∑ _i : I, ENNReal.ofReal (L / B) := Finset.sum_le_sum fun i _ => hinner i
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring
  refine ⟨E, hE, hsub, ?_, ?_⟩
  · have hEfin : μ E ≠ ∞ := ne_top_of_le_ne_top hAfin (measure_mono hsub)
    apply ENNReal.le_of_add_le_add_right hEfin
    calc
      _ = μ A := by
        have h := measure_sdiff_add_inter A hE (μ := μ)
        rwa [Set.inter_eq_right.mpr hsub] at h
      _ ≤ μ E + ∑ ic ∈ S, τ ic := hmass
      _ ≤ _ := by simpa only [add_comm] using add_le_add_left hsum (μ E)
  · intro i p hp
    have hmem : (⟨i, code i p⟩ : Σ _ : I, C) ∈ S := by
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (hfinite i).mem_toFinset.mpr ⟨p, hsub hp, rfl⟩
    rcases hfloor _ hmem with hempty | hmass
    · exfalso
      have h : p ∈ E ∩ Cells ⟨i, code i p⟩ := ⟨hp,rfl⟩
      simp [hempty] at h
    · exact hmass

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
