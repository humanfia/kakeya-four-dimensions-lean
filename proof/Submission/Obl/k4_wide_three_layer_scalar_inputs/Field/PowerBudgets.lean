import Mathlib

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Field

noncomputable section

/-- The three approximation errors of the common-field menu fit its
prescribed accuracy at any sufficiently fine buffered physical chart. -/
theorem field_input_error_budget {N K H q σ V M B τ η : ℝ}
    (hN : 1 ≤ N) (hK : 0 < K) (_hH : 0 ≤ H) (hKN : K ≤ N ^ σ) (hHN : H ≤ N ^ σ)
    (hq : N ^ (-V) / K ≤ q) (hB : σ + τ ≤ B)
    (hM : 2 * σ + V + τ ≤ M) (hM' : σ + τ ≤ M) (hconstant : 4 ≤ N ^ η) :
    N ^ (-τ) + H * (N ^ (-B) + N ^ (-M) / q + N ^ (-M)) ≤ N ^ η * N ^ (-τ) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hqlo : N ^ (-V - σ) ≤ q := by
    calc _ = N ^ (-V) / N ^ σ := by rw [← Real.rpow_sub hNp]
      _ ≤ N ^ (-V) / K := div_le_div_of_nonneg_left (Real.rpow_nonneg hNp.le _) hK hKN
      _ ≤ q := hq
  have hq0 : 0 < q := (Real.rpow_pos_of_pos hNp _).trans_le hqlo
  have hcell : H * N ^ (-B) ≤ N ^ (-τ) := by
    calc _ ≤ N ^ σ * N ^ (-B) := mul_le_mul_of_nonneg_right hHN (Real.rpow_nonneg hNp.le _)
      _ = N ^ (σ - B) := by rw [← Real.rpow_add hNp]; congr 1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hchart : H * (N ^ (-M) / q) ≤ N ^ (-τ) := by
    calc _ ≤ N ^ σ * (N ^ (-M) / N ^ (-V - σ)) := by
          gcongr
      _ = N ^ (2 * σ + V - M) := by
          rw [← Real.rpow_sub hNp, ← Real.rpow_add hNp]
          congr 1
          ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hvelocity : H * N ^ (-M) ≤ N ^ (-τ) := by
    calc _ ≤ N ^ σ * N ^ (-M) := mul_le_mul_of_nonneg_right hHN (Real.rpow_nonneg hNp.le _)
      _ = N ^ (σ - M) := by rw [← Real.rpow_add hNp]; congr 1
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hfour : 4 * N ^ (-τ) ≤ N ^ η * N ^ (-τ) :=
    mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hNp.le _)
  nlinarith

/-- A single small loss bounds the field's finite menu size, coefficient
norms, and original block velocity terms. -/
theorem field_input_coefficient_budget {N K H σ η : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (_hH : 0 ≤ H) (hKN : K ≤ N ^ σ) (hHN : H ≤ N ^ σ)
    (hbudget : 8 * N ^ (2 * σ) ≤ N ^ η) :
    3 * K ≤ N ^ η ∧ H * (5 + 3 * K) ≤ N ^ η := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hp : 1 ≤ N ^ σ := hK.trans hKN
  have hsq : (N ^ σ) ^ 2 = N ^ (2 * σ) := by
    rw [← Real.rpow_mul_natCast hNp.le]
    congr 1
    ring
  constructor
  · have hmul := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ N ^ σ)
    nlinarith
  · calc _ ≤ N ^ σ * (8 * N ^ σ) := by
          apply mul_le_mul hHN (by nlinarith) (by positivity) (Real.rpow_nonneg hNp.le _)
      _ = 8 * N ^ (2 * σ) := by rw [← hsq]; ring
      _ ≤ _ := hbudget

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Field
