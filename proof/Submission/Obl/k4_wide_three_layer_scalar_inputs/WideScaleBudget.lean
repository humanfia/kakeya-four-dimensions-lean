import Submission.Obl.k4_wide_three_layer_scalar_inputs.OffsetFreezing

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter

/-- The supplied strict wide margins pay the variation on the actual
coarse time interval and transverse key width, in original physical units. -/
theorem eventually_short_wide_bound {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {d κ s₀ s u σ : ℝ} (hu : 0 < u) (hσ : 0 < σ) (hσu : σ ≤ u / 10)
    (hwide : (10 / (1 - d) + 3) * u < 2 * κ * (s - s₀))
    (hblock : (10 / (1 - d) + 3) * u < κ * s) :
    ∀ᶠ k in atTop, ∀ K q : ℝ, K ≤ N k ^ σ → q ≤ K * N k ^ (-κ * s) →
      98304 * (N k ^ (σ + (10 / (1 - d)) * u) * N k ^ (-s)) *
        (q + (q * N k ^ (-κ * s)) / N k ^ (-2 * κ * s₀)) ≤ N k ^ (-(s + u)) := by
  filter_upwards [eventually_wide_freezing_with_constant hNt 98304 hu hσu hwide hblock]
    with k hk
  intro K q hK hq
  have hNp : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hqb : q ≤ N k ^ σ * N k ^ (-κ * s) :=
    hq.trans (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hNp.le _))
  have ht1 : q ≤ N k ^ (-κ * s + σ) := by
    convert hqb using 1
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have ht2 : q * N k ^ (-κ * s) / N k ^ (-2 * κ * s₀) ≤
      N k ^ (-2 * κ * (s - s₀) + 2 * σ) := by
    calc _ ≤ ((N k ^ σ * N k ^ (-κ * s)) * N k ^ (-κ * s)) /
          N k ^ (-2 * κ * s₀) := by gcongr
      _ = N k ^ (-2 * κ * (s - s₀) + σ) := by
          rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_sub hNp]
          congr 1
          ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc _ = N k ^ (-s) * (98304 * N k ^ (σ + (10 / (1 - d)) * u) *
        (q + (q * N k ^ (-κ * s)) / N k ^ (-2 * κ * s₀))) := by ring
    _ ≤ N k ^ (-s) * (98304 * N k ^ (σ + (10 / (1 - d)) * u) *
        (N k ^ (-κ * s + σ) + N k ^ (-2 * κ * (s - s₀) + 2 * σ))) := by gcongr
    _ ≤ N k ^ (-s) * N k ^ (-u) := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring

end Submission.Obl.k4_wide_three_layer_scalar_inputs
