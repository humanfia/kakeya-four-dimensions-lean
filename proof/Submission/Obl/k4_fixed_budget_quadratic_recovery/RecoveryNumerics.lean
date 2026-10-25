import Submission.Obl.k4_fixed_budget_quadratic_recovery.OutputNumerics

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open Filter

/-- All analytic and output losses for scalar recovery are absorbed with fixed
positive gaps. The internal fit exponent is chosen before the external input loss. -/
theorem eventually_recovery_bounds
    {s θ e ε a δ η η₀ : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hθe : θ ≤ e)
    (ha : 0 ≤ a) (haκ : a ≤ s * θ / 100) (haε : a < ε)
    (hδκ : δ ≤ s * θ / 100) (hηκ : η ≤ s * θ / 100) (hη₀ : η < η₀) :
    ∀ᶠ N : ℝ in atTop,
      (24 * N ^ (a + 2 * η) ≤ N ^ (s * e)) ∧
      (4 * N ^ (δ - s) ≤ N ^ (s * (-1 + e))) ∧
      (864 * N ^ (-(s * e)) ≤ N ^ (-(s * θ / 2))) ∧
      (112 * N ^ (a + δ + 2 * η - 2 * s * e) ≤ N ^ (-η)) ∧
      (4 * N ^ (-η₀) ≤ N ^ (-η)) ∧
      (6 * (N ^ a + N ^ (-(s * θ / 2))) ≤ N ^ ε) ∧
      (48 * N ^ (-(s * θ / 2)) * (N ^ η) ^ (2 : ℕ) ≤ N ^ (-(s * θ / 4))) := by
  have hse : s * θ ≤ s * e := mul_le_mul_of_nonneg_left hθe hs.le
  have hsθ : 0 < s * θ := mul_pos hs hθ
  have h₁ := eventually_const_mul_rpow_le 24
    (show a + 2 * η < s * e by linarith)
  have h₂ := eventually_const_mul_rpow_le 4
    (show δ - s < s * (-1 + e) by nlinarith)
  have h₃ := eventually_const_mul_rpow_le 864
    (show -(s * e) < -(s * θ / 2) by linarith)
  have h₄ := eventually_const_mul_rpow_le 112
    (show a + δ + 2 * η - 2 * s * e < -η by linarith)
  have h₅ := eventually_const_mul_rpow_le 4 (neg_lt_neg hη₀)
  have h₆ := eventually_rounded_coeff_bound ha haε
  have h₇ := eventually_rounding_fit_bound
    (r := s * θ / 2) (c := s * θ / 4) (e := η)
    (show 2 * η < s * θ / 2 - s * θ / 4 by linarith)
  filter_upwards [h₁, h₂, h₃, h₄, h₅, h₆, h₇, eventually_ge_atTop (1 : ℝ)]
    with N h₁N h₂N h₃N h₄N h₅N h₆N h₇N hN
  have hr : 0 < s * θ / 2 := by positivity
  have hρ : N ^ (-(s * θ / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  exact ⟨h₁N, h₂N, h₃N, h₄N, h₅N, h₆N _ hρ, h₇N η le_rfl⟩

end Submission.Obl.k4_fixed_budget_quadratic_recovery
