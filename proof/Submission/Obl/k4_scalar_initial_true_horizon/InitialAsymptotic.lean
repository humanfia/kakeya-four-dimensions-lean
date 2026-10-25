import Mathlib

/-!
# Elementary asymptotics along a resolution sequence

Powers of a resolution `N k → ∞` eventually dominate constants and logarithms, and dyadic
ceilings of `a log₂ N` give powers of two comparable to `N^a`.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open Filter Topology

theorem eventually_const_le_rpow {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) {a : ℝ} (ha : 0 < a)
    (C : ℝ) : ∀ᶠ k in atTop, C ≤ N k ^ a :=
  ((tendsto_rpow_atTop ha).comp hN).eventually (eventually_ge_atTop C)

theorem eventually_logb_le_rpow {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) {a : ℝ} (ha : 0 < a)
    (C : ℝ) : ∀ᶠ k in atTop, C * Real.logb 2 (N k) ≤ N k ^ a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / (|C| + 1) := by positivity
  have hbound := ((isLittleO_log_rpow_atTop ha).bound hc)
  filter_upwards [hN.eventually hbound, hN.eventually (eventually_ge_atTop 1)] with k hk hk1
  have hpos : 0 ≤ N k ^ a := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos] at hk
  have hlogk : 0 ≤ Real.log (N k) := Real.log_nonneg hk1
  rw [abs_of_nonneg hlogk] at hk
  rw [Real.logb]
  calc C * (Real.log (N k) / Real.log 2) ≤ |C| * (Real.log (N k) / Real.log 2) := by
        gcongr; exact le_abs_self C
    _ ≤ (|C| + 1) * (Real.log (N k) / Real.log 2) := by
        gcongr; linarith
    _ = Real.log (N k) / (Real.log 2 / (|C| + 1)) := by field_simp
    _ ≤ N k ^ a := by
        rw [div_le_iff₀ hc]; linarith [mul_comm (Real.log 2 / (|C| + 1)) (N k ^ a)]

/-- `2 ^ ⌈a log₂ x⌉₊ ≥ x ^ a`. -/
theorem two_pow_ceil_logb_ge {x a : ℝ} (hx : 0 < x) :
    x ^ a ≤ (2 : ℝ) ^ ⌈a * Real.logb 2 x⌉₊ := by
  have h1 : x ^ a = (2 : ℝ) ^ (a * Real.logb 2 x) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx]
  rw [h1, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)

/-- `2 ^ ⌈a log₂ x⌉₊ ≤ 2 x ^ a` when the exponent is nonnegative. -/
theorem two_pow_ceil_logb_le {x a : ℝ} (hx : 0 < x) (hpos : 0 ≤ a * Real.logb 2 x) :
    (2 : ℝ) ^ ⌈a * Real.logb 2 x⌉₊ ≤ 2 * x ^ a := by
  have h1 : x ^ a = (2 : ℝ) ^ (a * Real.logb 2 x) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx]
  rw [h1, ← Real.rpow_natCast]
  have hlt := Nat.ceil_lt_add_one hpos
  calc (2 : ℝ) ^ (⌈a * Real.logb 2 x⌉₊ : ℝ) ≤ (2 : ℝ) ^ (a * Real.logb 2 x + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
    _ = 2 * (2 : ℝ) ^ (a * Real.logb 2 x) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]

/-- The ceiling exponent itself is at most `a log₂ x + 1`. -/
theorem ceil_logb_le {x a : ℝ} (hpos : 0 ≤ a * Real.logb 2 x) :
    (⌈a * Real.logb 2 x⌉₊ : ℝ) ≤ a * Real.logb 2 x + 1 :=
  (Nat.ceil_lt_add_one hpos).le

end Submission.Obl.k4_scalar_initial_true_horizon
