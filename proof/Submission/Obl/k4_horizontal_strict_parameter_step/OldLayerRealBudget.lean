/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OldLayerRealBudget.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OldLayerBudgets
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Mass
import Submission.Obl.k4_row_cell_regularization.Palette

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_row_cell_regularization

/-- In real palette units, a whole old layer has a summed reference budget
bounded by its source mass times its original loss. -/
theorem LayerAt.reference_budget_real {α : Type} [MeasurableSpace α]
    {N : ℕ → ℝ} {d e₀ : ℝ} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {k : ℕ} {ε D a M : ℝ}
    {ρH : Measure (α × ℝ)} {n : ℕ} {A : Fin n → Set α}
    {q : Fin n → Fin 3 → ℤ} {h : Fin n → Fin 6 → ℝ}
    (H : LayerAt N d e₀ π b k ε ρH D a n A q h)
    [IsProbabilityMeasure (π k)] (hN : 0 < N k) (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hmass : ρH univ ≤ ENNReal.ofReal M) :
    (∑ i, D ^ 2 * a ^ d * binWeight (π k) (N k ^ (-e₀)) (q i 0)) ≤ N k ^ ε * M := by
  have hX : 0 ≤ D ^ 2 * a ^ d := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ha _)
  have hp : 0 < N k ^ ε := Real.rpow_pos_of_pos hN _
  apply Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.original_reference_budget
    ρH Finset.univ (fun i => A i ×ˢ Icc (0 : ℝ) 1)
    (fun i => D ^ 2 * a ^ d * binWeight (π k) (N k ^ (-e₀)) (q i 0)) hp hM
    (fun i _ => mul_nonneg hX (binWeight_nonneg _ _ _))
    (fun i _ => (H.1 i).prod measurableSet_Icc)
    (fun i _ j _ hij => (H.2.1 i j hij).set_prod_left _ _) ?_ hmass
  intro i hi
  calc
    _ = ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε) *
        ENNReal.ofReal (binWeight (π k) (N k ^ (-e₀)) (q i 0)) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hX hp.le)]
      congr 1
      ring
    _ = ENNReal.ofReal (D ^ 2 * a ^ d / N k ^ ε) *
        π k (Ico ((q i 0 : ℝ) * N k ^ (-e₀)) (((q i 0 : ℝ) + 1) * N k ^ (-e₀))) := by
      rw [binWeight, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := (H.2.2.1 i).2.2.2

end Submission.Obl.k4_horizontal_strict_parameter_step
