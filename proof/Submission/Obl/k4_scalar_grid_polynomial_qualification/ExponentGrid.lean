import Submission.Obl.k4_scalar_grid_polynomial_qualification.Model

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

noncomputable section

def upperGridExponent (J : ℕ) (r : ℝ) : ℝ := (⌈r * (J : ℝ)⌉₊ : ℝ) / (J : ℝ)

theorem upperGridExponent_bounds {J : ℕ} (hJ : 1 ≤ J) {r : ℝ} (hr : 0 ≤ r) :
    r ≤ upperGridExponent J r ∧ upperGridExponent J r < r + 1 / (J : ℝ) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hlo := Nat.le_ceil (r * (J : ℝ))
  have hhi := Nat.ceil_lt_add_one (mul_nonneg hr hJ0.le)
  constructor
  · exact (le_div_iff₀ hJ0).2 hlo
  · apply (div_lt_iff₀ hJ0).2
    convert hhi using 1; field_simp

theorem upperGridExponent_on_grid (J : ℕ) (r : ℝ) :
    ∃ m : ℕ, upperGridExponent J r = (m : ℝ) / (J : ℝ) := ⟨_, rfl⟩

/-- Every requested exponent can be replaced by an available finer exponent
with a width ratio paid for by the frozen mesh cost. -/
theorem grid_width_comparison {N H : ℝ} (hN : 1 ≤ N) {J : ℕ} (hJ : 1 ≤ J)
    (hcost : N ^ ((1 : ℝ) / (J : ℝ)) ≤ H) {r : ℝ} (hr : 0 ≤ r) :
    N ^ (-upperGridExponent J r) ≤ N ^ (-r) ∧
      N ^ (-r) / N ^ (-upperGridExponent J r) ≤ H := by
  have hN0 : 0 < N := by linarith
  have hg := upperGridExponent_bounds hJ hr
  refine ⟨Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hg.1), ?_⟩
  rw [← Real.rpow_sub hN0]
  exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith [hg.2])).trans hcost

theorem grid_step_le_of_cost {N H ε : ℝ} (hN : 1 < N) {J : ℕ}
    (hcost : N ^ ((1 : ℝ) / (J : ℝ)) ≤ H) (hH : H ≤ N ^ ε) :
    (1 : ℝ) / (J : ℝ) ≤ ε :=
  (Real.rpow_le_rpow_left_iff hN).1 (hcost.trans hH)

theorem eventually_grid_step_le {N H : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k)
    (hH : Subpower N H) (J : ℕ → ℕ)
    (hcost : ∀ k, N k ^ ((1 : ℝ) / (J k : ℝ)) ≤ H k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (1 : ℝ) / (J k : ℝ) ≤ ε := by
  filter_upwards [hH.2 ε hε] with k hk
  exact grid_step_le_of_cost (by linarith [hN k]) (hcost k) hk

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification
