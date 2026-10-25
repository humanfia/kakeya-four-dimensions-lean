import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- A fixed finite collection of floors costs less than a dense retained law
when every source loss is small relative to the final requested loss. -/
theorem eventually_common_layer_reserve (m : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hgap : 3 * δ < ε) :
    ∀ᶠ N : ℝ in atTop, 2 ≤ N ∧
      N ^ (-ε) + (m : ℝ) * N ^ (2 * δ - ε) < N ^ (-δ) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_const_mul_rpow_le (2 * ((m : ℝ) + 1))
      (a := 2 * δ - ε) (b := -δ) (by linarith)] with N hN hsmall
  have hNp : 0 < N := by linarith
  have hp : 0 < N ^ (2 * δ - ε) := Real.rpow_pos_of_pos hNp _
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hfirst : N ^ (-ε) ≤ N ^ (2 * δ - ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  refine ⟨hN, ?_⟩
  calc
    _ ≤ ((m : ℝ) + 1) * N ^ (2 * δ - ε) := by nlinarith
    _ < (2 * ((m : ℝ) + 1)) * N ^ (2 * δ - ε) := by nlinarith
    _ ≤ N ^ (-δ) := hsmall

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
