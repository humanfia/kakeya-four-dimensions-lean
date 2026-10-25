import Submission.Obl.k4_wide_three_layer_scalar_inputs.Field.PowerBudgets
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Field.CellBudget
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Field

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- Capturing the consensus field at a strictly finer accuracy than the
layer-2 mesh costs only a polynomial in the original geometric constants. -/
theorem field_recovery_error_budget {N H K σ B τ ε v : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hK : 1 ≤ K) (hHN : H ≤ N ^ σ)
    (hε : ε + v ≤ τ) (hv : v ≤ τ) (hB : σ + v ≤ B) :
    H * N ^ (-v) + (N ^ ε * N ^ (-τ) + N ^ (-τ) + H * N ^ (-B)) *
      (K + K ^ 2) ≤ (8 * H * K ^ 2) * N ^ (-v) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hE : N ^ ε * N ^ (-τ) ≤ N ^ (-v) := by
    rw [← Real.rpow_add hNp]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have heR : N ^ (-τ) ≤ N ^ (-v) :=
    Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hv)
  have hδ : H * N ^ (-B) ≤ N ^ (-v) := by
    calc _ ≤ N ^ σ * N ^ (-B) := mul_le_mul_of_nonneg_right hHN (by positivity)
      _ = N ^ (σ - B) := by rw [← Real.rpow_add hNp]; congr 1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have hHsq : K ^ 2 ≤ H * K ^ 2 := le_mul_of_one_le_left (sq_nonneg K) hH
  have hHbase : H ≤ H * K ^ 2 := by nlinarith
  calc _ ≤ H * N ^ (-v) + (3 * N ^ (-v)) * (K + K ^ 2) := by gcongr; linarith
    _ = (H + 3 * (K + K ^ 2)) * N ^ (-v) := by ring
    _ ≤ (8 * H * K ^ 2) * N ^ (-v) := by gcongr; nlinarith

/-- All common-field coefficient, full-reference cap and corrected-fit
costs hold uniformly below independent subpower geometric constants. -/
theorem eventually_field_native_budgets {σ η d s M B τ ε v m : ℝ}
    (hσ : 0 < σ) (hη : 0 < η) (hd : d ≤ 1)
    (hcoeff : 2 * σ < η) (hcap : 6 * σ ≤ η)
    (hB : σ + τ ≤ B) (hM : 2 * σ + s + τ ≤ M) (hM' : σ + τ ≤ M)
    (hε : ε + v ≤ τ) (hv : v ≤ τ) (hBv : σ + v ≤ B)
    (hout : 5 * σ + v < m) :
    ∀ᶠ N : ℝ in atTop, ∀ K H q : ℝ,
      1 ≤ K → 1 ≤ H → K ≤ N ^ σ → H ≤ N ^ σ → N ^ (-s) / K ≤ q →
      3 * K ≤ N ^ η ∧ H * (5 + 3 * K) ≤ N ^ η ∧
      N ^ (-τ) + H * (N ^ (-B) + N ^ (-M) / q + N ^ (-M)) ≤ N ^ η * N ^ (-τ) ∧
      2250 * K ^ 3 * (N ^ (-(s - 2 * σ))) ^ d ≤ N ^ η * (N ^ (-s)) ^ d ∧
      H * N ^ (-v) + (N ^ ε * N ^ (-τ) + N ^ (-τ) + H * N ^ (-B)) *
        (K + K ^ 2) ≤ (8 * H * K ^ 2) * N ^ (-v) ∧
      8 * H * K ^ 2 ≤ N ^ (4 * σ) ∧
      (8 * H * K ^ 2) * (5 + 3 * K) * N ^ (-m) ≤ N ^ (-v) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_rpow_le 4 (a := 0) hη,
    eventually_const_mul_rpow_le 8 hcoeff,
    eventually_const_mul_rpow_le 2250 (a := 0) hσ,
    eventually_const_mul_rpow_le 8 (a := 0) hσ,
    eventually_const_mul_rpow_le 8 (a := 5 * σ - m) (b := -v) (by linarith)]
    with N hN hfour hcoef h2250 height hlast
  have hNp : 0 < N := zero_lt_one.trans_le hN
  simp only [Real.rpow_zero, mul_one] at hfour h2250 height
  intro K H q hK hH hKN hHN hq
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  obtain ⟨hKη, hHη⟩ := field_input_coefficient_budget hN hK hH0 hKN hHN hcoef
  have hfull : 2250 * K ^ 3 * (N ^ (-(s - 2 * σ))) ^ d ≤ N ^ η * (N ^ (-s)) ^ d :=
    field_cell_budget_power hN (zero_le_one.trans hK) hKN h2250 (by
      have hh := mul_le_mul_of_nonneg_right hd (show 0 ≤ 2 * σ by linarith)
      nlinarith)
  have hpow : N ^ σ * (N ^ σ) ^ 2 = N ^ (3 * σ) := by
    rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_add hNp]
    congr 1
    ring
  have hheight : 8 * H * K ^ 2 ≤ N ^ (4 * σ) := by
    calc _ ≤ 8 * N ^ σ * (N ^ σ) ^ 2 := by gcongr
      _ = 8 * N ^ (3 * σ) := by rw [mul_assoc, hpow]
      _ ≤ N ^ σ * N ^ (3 * σ) := mul_le_mul_of_nonneg_right height (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  have hmesh : (8 * H * K ^ 2) * (5 + 3 * K) * N ^ (-m) ≤ N ^ (-v) := by
    calc _ ≤ N ^ (4 * σ) * (8 * N ^ σ) * N ^ (-m) := by
          gcongr
          have hone : 1 ≤ N ^ σ := hK.trans hKN
          nlinarith
      _ = 8 * (N ^ (4 * σ) * N ^ σ * N ^ (-m)) := by ring
      _ = 8 * N ^ (5 * σ - m) := by
          rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]
          congr 1
          ring
      _ ≤ _ := hlast
  exact ⟨hKη, hHη, field_input_error_budget hN hKp hH0 hKN hHN hq hB hM hM' hfour,
    hfull, field_recovery_error_budget hN hH hK hHN hε hv hBv, hheight, hmesh⟩

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Field
