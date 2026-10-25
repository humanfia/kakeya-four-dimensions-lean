/- Adapted from this LOT tree, obligation o245, session x0854,
branch x0854 at ba3817bb17b771a5ddd349237fa63f3fef2ba670, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeDensityBudget.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativePairBudget
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeFrameSupport

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The actual continuous matching densities have a total budget paid by the
original old and native priors. Widening the graph tolerance costs only the
corresponding fractional power, with the palette unchanged. -/
theorem observed_matching_density_budget {k : ℕ} {s D ε A : ℝ}
    (a : cfg.AssignmentLevel k s) (hbasic : cfg.Basic)
    (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k) (hℓ : cfg.ℓ = cfg.κ)
    (hD : 0 < D) (hDq : D ≤ cfg.timeLength k s ^ 2)
    (hχq : cfg.N k ^ (-cfg.e₀) ≤ cfg.timeLength k s ^ 2) (hA : 0 ≤ A)
    {m : ℕ} {AH : Fin m → Set α} {group : Fin m → Fin 3 → ℤ}
    {hH : Fin m → Fin 6 → ℝ} (σ : Measure (α × ℝ)) (hσ : σ ≤ cfg.μ k)
    (H : LayerAt cfg.N cfg.d cfg.e₀ cfg.π cfg.b k ε σ D (cfg.N k ^ (-s)) m AH group hH)
    {G : Set (α × ℝ)}
    (T : ObservedPairs G (fun i => AH i ×ˢ (univ : Set ℝ))
      (fun i => cfg.B k s i ×ˢ Data.I (cfg.T k s) (cfg.j k s i)))
    (hcontact : ∀ p ∈ G, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)) :
    (∑ i : T.Index group (cfg.j k s),
      (7 * (cfg.K k * A ^ cfg.d * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
        ((T.colour group (cfg.j k s) i).1 0))) *
      (4096 * cfg.timeLength k s * D ^ 2)) ≤
        (28672 * cfg.K k * (A / cfg.N k ^ (-s)) ^ cfg.d) *
          (cfg.N k ^ ε * cfg.K k + 128 * cfg.K k ^ 5) := by
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hpow : (A / cfg.N k ^ (-s)) ^ cfg.d * (cfg.N k ^ (-s)) ^ cfg.d = A ^ cfg.d := by
    rw [Real.div_rpow hA ha.le]
    exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos ha _).ne'
  calc
    _ = (28672 * cfg.K k * (A / cfg.N k ^ (-s)) ^ cfg.d) *
        ∑ i : T.Index group (cfg.j k s), cfg.timeLength k s * D ^ 2 *
          (cfg.N k ^ (-s)) ^ cfg.d * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀))
            ((T.colour group (cfg.j k s) i).1 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hpow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (cfg.observed_reference_budget a hbasic hN hK hℓ hD hDq hχq σ hσ H T hcontact)
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.rpow_nonneg
        (div_nonneg hA ha.le) _))

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
