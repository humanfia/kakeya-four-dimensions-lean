import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.NativeBounds

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter

namespace KeyFrame

/-- Fine physical fit and freezing errors normalize at the difference of the two
original depths. The fixed key horizon also fits within that accuracy. -/
theorem normalized_fine_error_budget {N K H s w M : ℝ} (hN : 1 ≤ N)
    (hbudget : 2 * K + 1 ≤ H) (hw : w ≤ M / 2) :
    (2 * K * N ^ (-(s + w))) / N ^ (-s) + N ^ (-M / 2) ≤ H * N ^ (-w) := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hid : (2 * K * N ^ (-(s + w))) / N ^ (-s) = 2 * K * N ^ (-w) := by
    rw [mul_div_assoc, ← Real.rpow_sub hN₀]
    congr 2
    ring
  have hchart : N ^ (-M / 2) ≤ N ^ (-w) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  rw [hid]
  calc
    _ ≤ 2 * K * N ^ (-w) + N ^ (-w) := add_le_add le_rfl hchart
    _ = (2 * K + 1) * N ^ (-w) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hN₀.le _)

/-- One eventual index pays both complete coefficient budgets and every finer-depth
fit budget. Its original depth difference is arbitrary below `M/2`, so it applies to
both projected colors simultaneously. -/
theorem eventually_prediction_output_budgets {η ξ ε : ℝ}
    (hη : 0 ≤ η) (hcoeff : ξ + 8 * η < ε) (hfit : η < ε) :
    ∀ᶠ N : ℝ in atTop, ∀ K Mst : ℝ,
      1 ≤ K → K ≤ N ^ η → 0 ≤ Mst → Mst ≤ N ^ ξ →
      3888 * Mst * K ^ 8 ≤ N ^ ε ∧
      ∀ s w M : ℝ, w ≤ M / 2 →
        (2 * K * N ^ (-(s + w))) / N ^ (-s) + N ^ (-M / 2) ≤
          N ^ ε * N ^ (-w) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_native_coefficient_budget hcoeff,
    Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 3 hfit]
    with N hN hc hf
  intro K Mst hK hKN hMst hMstN
  refine ⟨hc K Mst hK hMst hKN hMstN, ?_⟩
  have hone : 1 ≤ N ^ η := Real.one_le_rpow hN hη
  have hbudget : 2 * K + 1 ≤ N ^ ε := by linarith
  intro s w M hw
  exact normalized_fine_error_budget hN hbudget hw

end KeyFrame

end Submission.Obl.k4_wide_three_layer_scalar_inputs
