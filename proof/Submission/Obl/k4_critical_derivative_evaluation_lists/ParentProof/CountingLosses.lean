/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, CountingLosses.lean.
   Original source attributions below are retained. -/

import Mathlib

/-! Elementary deletion budgets for the coefficient count: atypical groups are
charged to the trajectory prior, light subbin entries to their floors. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal

/-- Groups whose prior exceeds `L` times their weight carry little mass when
the group mass is at most `C` times the weight. -/
theorem atypical_group_loss {α Ω ι : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (ν : Measure α) [IsProbabilityMeasure ν] (ρ : Measure Ω)
    (S : Finset ι) (X : ι → Set α) (D : ι → Set Ω) (W : ι → ℝ) (C L : ℝ)
    (hX : ∀ g ∈ S, MeasurableSet (X g)) (hdisj : (↑S : Set ι).PairwiseDisjoint X)
    (hC : 0 ≤ C) (hL : 0 < L) (hW : ∀ g, 0 ≤ W g)
    (hmass : ∀ g ∈ S, ρ (D g) ≤ ENNReal.ofReal (C * W g))
    (hbad : ∀ g ∈ S, W g = 0 ∨ L * W g < ν.real (X g)) :
    ρ (⋃ g ∈ S, D g) ≤ ENNReal.ofReal (C / L) := by
  have hterm : ∀ g ∈ S, ρ (D g) ≤ ENNReal.ofReal (C / L * ν.real (X g)) := by
    intro g hg
    refine (hmass g hg).trans (ENNReal.ofReal_le_ofReal ?_)
    rcases hbad g hg with h0 | hlt
    · rw [h0, mul_zero]; positivity
    · have : W g ≤ ν.real (X g) / L := by
        rw [le_div_iff₀ hL]; linarith
      calc
        C * W g ≤ C * (ν.real (X g) / L) := mul_le_mul_of_nonneg_left this hC
        _ = C / L * ν.real (X g) := by ring
  have hsum : ∑ g ∈ S, ν.real (X g) ≤ 1 := by
    rw [← measureReal_biUnion_finset hdisj hX]
    exact (measureReal_mono (subset_univ _)).trans (by simp)
  calc
    ρ (⋃ g ∈ S, D g) ≤ ∑ g ∈ S, ρ (D g) := measure_biUnion_finset_le _ _
    _ ≤ ∑ g ∈ S, ENNReal.ofReal (C / L * ν.real (X g)) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ g ∈ S, C / L * ν.real (X g)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro g _
      exact mul_nonneg (div_nonneg hC hL.le) measureReal_nonneg
    _ ≤ ENNReal.ofReal (C / L) := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      calc
        C / L * ∑ g ∈ S, ν.real (X g) ≤ C / L * 1 :=
          mul_le_mul_of_nonneg_left hsum (div_nonneg hC hL.le)
        _ = C / L := mul_one _

/-- Light entries, each below its floor `φ g`, cost at most the number of
entries times the floors. -/
theorem light_entry_loss {Ω ι κ τ : Type*} [MeasurableSpace Ω] (ρ : Measure Ω)
    (S : Finset ι) (HC : ι → Finset κ) (Θ : Finset τ) (cell : ι → κ → τ → Set Ω)
    (φ : ι → ℝ) (hφ : ∀ g, 0 ≤ φ g) :
    ρ (⋃ g ∈ S, ⋃ q ∈ HC g, ⋃ θ ∈ Θ.filter (fun θ => ρ (cell g q θ) < ENNReal.ofReal (φ g)),
        cell g q θ) ≤
      ENNReal.ofReal (∑ g ∈ S, ((HC g).card : ℝ) * (Θ.card : ℝ) * φ g) := by
  classical
  calc
    _ ≤ ∑ g ∈ S, ρ (⋃ q ∈ HC g, ⋃ θ ∈ Θ.filter
        (fun θ => ρ (cell g q θ) < ENNReal.ofReal (φ g)), cell g q θ) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ g ∈ S, ∑ q ∈ HC g, ρ (⋃ θ ∈ Θ.filter
        (fun θ => ρ (cell g q θ) < ENNReal.ofReal (φ g)), cell g q θ) :=
      Finset.sum_le_sum (fun g _ => measure_biUnion_finset_le _ _)
    _ ≤ ∑ g ∈ S, ∑ q ∈ HC g, ∑ θ ∈ Θ.filter
        (fun θ => ρ (cell g q θ) < ENNReal.ofReal (φ g)), ρ (cell g q θ) :=
      Finset.sum_le_sum (fun g _ => Finset.sum_le_sum (fun q _ => measure_biUnion_finset_le _ _))
    _ ≤ ∑ g ∈ S, ∑ q ∈ HC g, ∑ _θ ∈ Θ, ENNReal.ofReal (φ g) := by
      apply Finset.sum_le_sum; intro g _
      apply Finset.sum_le_sum; intro q _
      calc
        _ ≤ ∑ θ ∈ Θ.filter (fun θ => ρ (cell g q θ) < ENNReal.ofReal (φ g)),
            ENNReal.ofReal (φ g) :=
          Finset.sum_le_sum (fun θ hθ => (Finset.mem_filter.mp hθ).2.le)
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ENNReal.ofReal (∑ g ∈ S, ((HC g).card : ℝ) * (Θ.card : ℝ) * φ g) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun g _ => by have := hφ g; positivity)]
      apply Finset.sum_congr rfl
      intro g _
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      ring

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
