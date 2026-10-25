/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/BlockSignal.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.WitnessInheritance

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-- The selected coarse native entry is fixed on each original time block. -/
def blockSignal (T : ℕ) (row : Fin (2 ^ T) → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ j, (I T j).indicator (row j) t

theorem measurable_blockSignal (T : ℕ) (row : Fin (2 ^ T) → ℝ → ℝ)
    (hrow : ∀ j, Measurable (row j)) : Measurable (blockSignal T row) := by
  unfold blockSignal
  apply Finset.measurable_sum
  intro j _
  exact (hrow j).indicator measurableSet_Icc

/-- Although the blocks are closed, the summed piecewise signal equals its
named block row almost everywhere for the original product-dominated law. -/
theorem blockSignal_eq_row_ae {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ)) (C : ENNReal)
    (hdom : μ ≤ C • (ν.prod volume)) (T : ℕ) (row : Fin (2 ^ T) → ℝ → ℝ) :
    ∀ᵐ p ∂μ, ∀ j, p.2 ∈ I T j → blockSignal T row p.2 = row j p.2 := by
  have hu := true_assignments_ae_unique ν μ C hdom T id
    (fun _ : Fin (2 ^ T) => (univ : Set α))
    (by intro i j hne hij; exact (hne hij).elim)
  filter_upwards [hu] with p hp
  intro j ht
  unfold blockSignal
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem ht _
  · intro i _ hne
    have hn : p.2 ∉ I T i := by
      intro hi
      exact hne (hp i j (mem_univ _) hi (mem_univ _) ht)
    exact Set.indicator_of_notMem hn _
  · simp

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
