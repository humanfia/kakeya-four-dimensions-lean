import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_horizontal_coefficient_count

open Filter

theorem canonical_buffer {U e₀ : ℝ} (hU : 0 < U) (he₀ : 0 < e₀) :
    0 < min (U / 4) (e₀ / 200) ∧
      2 * min (U / 4) (e₀ / 200) < U ∧
      100 * min (U / 4) (e₀ / 200) < e₀ := by
  have h₁ := min_le_left (U / 4) (e₀ / 200)
  have h₂ := min_le_right (U / 4) (e₀ / 200)
  exact ⟨by positivity, by linarith, by linarith⟩

/-- Power-decaying omitted mass and the final threshold budget are
eventually negligible compared with the original subpower mass floor. -/
theorem eventually_output_budget {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (m : ℕ) :
    ∀ᶠ k in atTop,
      N k ^ (-ε) + (m : ℝ) * N k ^ (-c) +
        (m : ℝ) * K k * N k ^ (-ε / 2) < (K k)⁻¹ := by
  have h₁ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 (show -ε < 0 by linarith) (show (0 : ℝ) ≤ 4 by norm_num)
  have h₂ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 (show -c < 0 by linarith)
    (show (0 : ℝ) ≤ 4 * m by positivity)
  have h₃ := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 2 (show -ε / 2 < 0 by linarith)
    (show (0 : ℝ) ≤ 4 * m by positivity)
  filter_upwards [h₁, h₂, h₃] with k hk₁ hk₂ hk₃
  simp only [pow_one, pow_two, Real.rpow_zero] at hk₁ hk₂ hk₃
  rw [← one_div, lt_div_iff₀ (show 0 < K k by linarith [hK k])]
  nlinarith

end Submission.Obl.k4_horizontal_coefficient_count
