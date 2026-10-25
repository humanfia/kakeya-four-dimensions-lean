import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics
import Submission.Obl.k4_quadratic_atlas_normalization.LowNumerics

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open Filter

/-- The original observation is finer than the scalar fitting scale. -/
theorem observation_error_le_scalar_fit {N η δ s : ℝ}
    (hN : 1 ≤ N) (hη : η ≤ δ) (hs : s ≤ 1) :
    N ^ (-1 + η) ≤ N ^ δ * N ^ (-s) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  rw [← Real.rpow_add hN0]
  apply Real.rpow_le_rpow_of_exponent_le hN
  linarith

/-- Grouping a polynomial number of seventh-power descriptions and adding the
coefficient box stays within a fixed thirteenth-power format budget. -/
theorem grouped_format_count {N n : ℝ} (hN : 2 ≤ N) (hn : n ≤ N ^ (2 : ℕ)) :
    10 + n * N ^ (7 : ℕ) ≤ N ^ (13 : ℕ) := by
  calc
    _ ≤ 10 + N ^ (2 : ℕ) * N ^ (7 : ℕ) := by gcongr
    _ = N ^ (9 : ℕ) + 10 := by ring
    _ ≤ _ := Submission.Obl.k4_quadratic_atlas_normalization.add_ten_budget hN 9

/-- Rounding by a width at most one preserves the requested coefficient allowance
when the original predictors use a strictly smaller exponent. -/
theorem eventually_rounded_coeff_bound {a ε : ℝ} (ha : 0 ≤ a) (haε : a < ε) :
    ∀ᶠ N : ℝ in atTop, ∀ ρ : ℝ, ρ ≤ 1 →
      6 * (N ^ a + ρ) ≤ N ^ ε := by
  filter_upwards [eventually_const_mul_rpow_le 12 haε,
    eventually_ge_atTop (1 : ℝ)] with N hC hN
  intro ρ hρ
  have hpow : 1 ≤ N ^ a := Real.one_le_rpow hN ha
  calc
    _ ≤ 12 * N ^ a := by linarith
    _ ≤ _ := hC

/-- A fixed rounding exponent absorbs all smaller coefficient-box exponents. -/
theorem eventually_rounding_fit_bound {r c e : ℝ} (hgap : 2 * e < r - c) :
    ∀ᶠ N : ℝ in atTop, ∀ η : ℝ, η ≤ e →
      48 * N ^ (-r) * (N ^ η) ^ (2 : ℕ) ≤ N ^ (-c) := by
  filter_upwards [eventually_const_mul_rpow_le 48
    (show -r + 2 * e < -c by linarith),
    eventually_ge_atTop (1 : ℝ)] with N hC hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  intro η hη
  calc
    _ = 48 * N ^ (-r + 2 * η) := by
      rw [← Real.rpow_mul_natCast hN0.le, mul_assoc, ← Real.rpow_add hN0]
      congr 2
      ring
    _ ≤ 48 * N ^ (-r + 2 * e) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hN
      linarith
    _ ≤ _ := hC

end Submission.Obl.k4_fixed_budget_quadratic_recovery
