import Mathlib

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Field

open scoped ENNReal

noncomputable section

/-- The original true-label floor cancels the entire geometric base volume.
The quantities `V` and `V'` are the old and slightly enlarged hidden widths
raised to the dimension. -/
theorem cell_cap_full_reference {K q g δ B V V' : ℝ} {prior : ℝ≥0∞}
    (hK : 0 < K) (hq : 0 ≤ q) (hg : 0 ≤ g) (hδ : 0 ≤ δ) (hδg : δ ≤ g)
    (hB : 0 ≤ B) (_hV : 0 ≤ V) (hV' : 0 ≤ V')
    (hbudget : 2250 * K ^ 3 * V' ≤ B * V)
    (hprior : ENNReal.ofReal (V * q ^ 2 * g / K) ≤ prior) :
    ENNReal.ofReal (6000 * K * (q * δ / 2) * (q * δ / 2) *
        (K * q * g + K * (q * δ / 2)) * V') ≤
      ENNReal.ofReal (B * δ ^ 2) * (ENNReal.ofReal q * prior) := by
  have hwidth : K * q * g + K * (q * δ / 2) ≤ (3 / 2 : ℝ) * K * q * g := by
    have := mul_le_mul_of_nonneg_left hδg (mul_nonneg hK.le hq)
    nlinarith
  have hreal : 6000 * K * (q * δ / 2) * (q * δ / 2) *
        (K * q * g + K * (q * δ / 2)) * V' ≤
      (B * δ ^ 2) * (q * (V * q ^ 2 * g / K)) := by
    calc _ ≤ 6000 * K * (q * δ / 2) * (q * δ / 2) *
          ((3 / 2 : ℝ) * K * q * g) * V' := by gcongr
      _ = (δ ^ 2 * q ^ 3 * g / K) * (2250 * K ^ 3 * V') := by
          field_simp
          ring
      _ ≤ (δ ^ 2 * q ^ 3 * g / K) * (B * V) :=
          mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by ring
  calc _ ≤ ENNReal.ofReal ((B * δ ^ 2) * (q * (V * q ^ 2 * g / K))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (B * δ ^ 2) *
        (ENNReal.ofReal q * ENNReal.ofReal (V * q ^ 2 * g / K)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hq]
    _ ≤ _ := by gcongr

/-- A small widening of the hidden window pays the original fit tolerance;
its dimension cost remains a subpower factor. -/
theorem field_cell_budget_power {N K η ξ s d κ : ℝ}
    (hN : 1 ≤ N) (hK0 : 0 ≤ K) (hK : K ≤ N ^ κ)
    (hconstant : 2250 ≤ N ^ κ) (hbudget : 4 * κ + d * ξ ≤ η) :
    2250 * K ^ 3 * (N ^ (-(s - ξ))) ^ d ≤ N ^ η * (N ^ (-s)) ^ d := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  calc _ ≤ N ^ κ * (N ^ κ) ^ 3 * (N ^ (-(s - ξ))) ^ d := by gcongr
    _ = N ^ (4 * κ + d * ξ - s * d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le, ← Real.rpow_mul hNp.le,
          ← Real.rpow_add hNp, ← Real.rpow_add hNp]
        congr 1
        push_cast
        ring
    _ ≤ N ^ (η + (-s) * d) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = _ := by rw [Real.rpow_add hNp, Real.rpow_mul hNp.le]

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Field
