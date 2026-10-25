import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open Filter

/-- One small exponent for the input system makes both exceptional losses
negligible relative to its inverse-slack mass, with a prescribed output slack. -/
theorem pruning_parameters {N : ℕ → ℝ} (hNt : Tendsto N atTop atTop)
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ ε / 100 ∧ σ ≤ c / 100 ∧
      ∀ᶠ k in atTop, ∀ κ : ℝ, 1 ≤ κ → κ ≤ N k ^ σ →
        2 * κ ≤ N k ^ (ε / 2) ∧ N k ^ (ε / 2) ≤ N k ^ ε ∧
          2 * N k ^ (-c) + 1024 * κ ^ 5 * N k ^ (ε / 100) / N k ^ (ε / 2) ≤
            (2 * κ)⁻¹ := by
  let σ := min (ε / 100) (c / 100)
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  have hσε : σ ≤ ε / 100 := min_le_left _ _
  have hσc : σ ≤ c / 100 := min_le_right _ _
  have hfirst := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := -c) (b := -σ) (by linarith) 8
  have hsecond := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := 5 * σ + ε / 100 - ε / 2) (b := -σ) (by linarith) 4096
  have hslack := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := σ) (b := ε / 2) (by linarith) 2
  refine ⟨σ, hσ, hσε, hσc, ?_⟩
  filter_upwards [hfirst, hsecond, hslack, hNt.eventually (eventually_ge_atTop 2)]
    with k hf hs hk hN
  intro κ hκ hκmax
  have hN0 : 0 < N k := by linarith
  have hN1 : 1 ≤ N k := by linarith
  have hκ0 : 0 < κ := by linarith
  have hθ0 : 0 < N k ^ (ε / 2) := Real.rpow_pos_of_pos hN0 _
  refine ⟨(mul_le_mul_of_nonneg_left hκmax (by norm_num : (0 : ℝ) ≤ 2)).trans hk.le,
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith), ?_⟩
  have hpower : (N k ^ σ) ^ (5 : ℕ) * N k ^ (ε / 100) / N k ^ (ε / 2) =
      N k ^ (5 * σ + ε / 100 - ε / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      ← Real.rpow_add hN0, ← Real.rpow_sub hN0]
    congr 1
    ring
  have hlarge : 1024 * κ ^ 5 * N k ^ (ε / 100) / N k ^ (ε / 2) ≤ N k ^ (-σ) / 4 := by
    calc
      _ ≤ 1024 * (N k ^ σ) ^ 5 * N k ^ (ε / 100) / N k ^ (ε / 2) := by gcongr
      _ = 1024 * N k ^ (5 * σ + ε / 100 - ε / 2) := by
        rw [mul_assoc, mul_div_assoc, hpower]
      _ ≤ _ := by linarith
  have hinv : N k ^ (-σ) ≤ κ⁻¹ := by
    rw [Real.rpow_neg hN0.le]
    simpa only [one_div] using one_div_le_one_div_of_le hκ0 hκmax
  have heq : (2 * κ)⁻¹ = κ⁻¹ / 2 := by ring
  rw [heq]
  linarith

end Submission.Obl.k4_coarsened_outer_horizon_composition
