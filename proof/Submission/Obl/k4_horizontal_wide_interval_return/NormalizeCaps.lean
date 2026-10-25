import Submission.Obl.k4_horizontal_wide_interval_return.CellCaps

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory
open scoped ENNReal

/-- Normalize physical cell volume against the full original true-label
floor. The factor `a^d` cancels, leaving the scalar cap `ρ^d`. -/
theorem cell_cap_normalization {a q g σ ρ d K D : ℝ}
    (ha : 0 < a) (hq : 0 < q) (hg : 0 < g) (hρ : 0 < ρ)
    (hK : 0 < K) (hD : 0 ≤ D) (mass weight : ℝ≥0∞)
    (hfloor : ENNReal.ofReal (a ^ d * q ^ 2 * g / K) ≤ mass) :
    ENNReal.ofReal (D * q ^ 3 * g * σ ^ 2 * (a * ρ) ^ d) * weight ≤
      ENNReal.ofReal (D * K * σ ^ 2 * ρ ^ d) * (ENNReal.ofReal q * mass) * weight := by
  have hnorm : 0 ≤ D * K * σ ^ 2 * ρ ^ d := by positivity
  have heq : D * q ^ 3 * g * σ ^ 2 * (a * ρ) ^ d =
      (D * K * σ ^ 2 * ρ ^ d) * q * (a ^ d * q ^ 2 * g / K) := by
    rw [Real.mul_rpow ha.le hρ.le]
    field_simp
  rw [heq, ENNReal.ofReal_mul (mul_nonneg hnorm hq.le), ENNReal.ofReal_mul hnorm]
  calc ((ENNReal.ofReal (D * K * σ ^ 2 * ρ ^ d) * ENNReal.ofReal q) *
      ENNReal.ofReal (a ^ d * q ^ 2 * g / K)) * weight
      ≤ ((ENNReal.ofReal (D * K * σ ^ 2 * ρ ^ d) * ENNReal.ofReal q) * mass) * weight := by
        gcongr
    _ = _ := by ring

/-- Convert the original power-form joint cell cap into the native physical
width form consumed by `cell_residual_cap`. -/
theorem native_rpow_cell_factor {N : ℝ} (hN : 0 < N) (B d s r : ℝ) :
    N ^ (-3 * B - d * (s + r)) =
      (N ^ (-B)) ^ (3 : ℕ) * (N ^ (-s) * N ^ (-r)) ^ d := by
  rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_add hN,
    ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
  congr 1
  ring

/-- Below a loss-dependent positive rate, the ordinary cap already supplies
the angular saving. This handles rates smaller than the fixed lower rate
allowed by one eventual original joint-cap assertion. -/
theorem angular_saving_at_small_rate {N η S r : ℝ} (hN : 1 ≤ N)
    (hr : S * r ≤ η / 2) : N ^ (η / 2) ≤ N ^ η * N ^ (-S * r) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  rw [← Real.rpow_add hNpos]
  exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end Submission.Obl.k4_horizontal_wide_interval_return
