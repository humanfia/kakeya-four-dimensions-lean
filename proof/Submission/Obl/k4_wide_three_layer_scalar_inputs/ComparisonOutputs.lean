import Submission.Obl.k4_wide_three_layer_scalar_inputs.WitnessBudgets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.OutputBudgets

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter

/-- Numerical losses in the complete output interface. All three list
counts and both fine fits use the same requested output loss. -/
structure ComparisonOutputs (N K d σ η ξ ε M : ℝ) : Prop where
  coarse : 14 * K * (N ^ (20 * η) * (N ^ ξ / (4 * N ^ η)) ^ d) ≤ N ^ ε
  fine : ∀ s Δ : ℝ,
    N ^ (20 * η) * (((16 * N ^ η * N ^ (-s) / N ^ (-(s + Δ))) / (4 * N ^ η))) ^ d ≤
      N ^ ε * N ^ (d * Δ)
  coefficients : 3888 * N ^ ξ * (N ^ σ) ^ 8 ≤ N ^ ε
  fit : ∀ s Δ : ℝ, Δ ≤ M / 2 →
    (2 * N ^ σ * N ^ (-(s + Δ))) / N ^ (-s) + N ^ (-M / 2) ≤ N ^ ε * N ^ (-Δ)
  radius : ∀ s Δ : ℝ, ξ ≤ Δ → N ^ ξ ≤ 16 * N ^ η * N ^ (-s) / N ^ (-(s + Δ))

theorem eventually_comparisonOutputs {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {d σ η ξ ε M : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hσ : 0 < σ) (hη : 0 < η) (hξ : 0 < ξ) (hση : 100 * σ ≤ η)
    (hgap : σ + 20 * η + ξ < ε) :
    ∀ᶠ k in atTop, ∀ K : ℝ, 1 ≤ K → K ≤ N k ^ σ →
      ComparisonOutputs (N k) K d σ η ξ ε M := by
  have hση' : σ < η := by linarith
  have hcoef : ξ + 8 * σ < ε := by linarith
  have hfit : σ < ε := by linarith
  filter_upwards [eventually_witness_card_budgets hN hNt hd0 hd1 hσ.le hη hξ hση' hgap,
    hNt.eventually (KeyFrame.eventually_prediction_output_budgets hσ.le hcoef hfit)]
      with k hc hp
  intro K hK hKN
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hP : 1 ≤ N k ^ σ := Real.one_le_rpow hN1 hσ.le
  have hpred := hp (N k ^ σ) (N k ^ ξ) hP le_rfl
    (Real.rpow_nonneg (by linarith [hN k]) _) le_rfl
  exact {
    coarse := hc.2.1 K (by linarith) hKN
    fine := hc.2.2.1
    coefficients := hpred.1
    fit := fun s Δ hΔ => hpred.2 s Δ M hΔ
    radius := hc.2.2.2 }

end Submission.Obl.k4_wide_three_layer_scalar_inputs
