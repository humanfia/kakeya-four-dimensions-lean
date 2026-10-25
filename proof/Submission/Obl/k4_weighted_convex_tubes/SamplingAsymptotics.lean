import Mathlib

namespace Submission.Obl.k4_weighted_convex_tubes

open Filter

/-- A power-size family of tests is absorbed by the exponential sampling tail. -/
theorem sampling_power_slack {τ B : ℝ} (hτ : 0 < τ) (hB : 0 < B) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      4 ≤ r ^ (-τ) / B ∧
      4 * B * r ^ (-B) ≤ Real.exp ((r ^ (-τ) / B) / 2) := by
  have ht := (tendsto_exp_mul_div_rpow_atTop (B / τ) (1 / (2 * B))
    (by positivity)).comp (tendsto_rpow_atTop hτ)
  have he := ht.eventually (eventually_ge_atTop (4 * B))
  have hp := (tendsto_rpow_atTop hτ).eventually (eventually_ge_atTop (4 * B))
  have hall : ∀ᶠ x : ℝ in atTop,
      4 ≤ x ^ τ / B ∧ 4 * B * x ^ B ≤ Real.exp ((x ^ τ / B) / 2) := by
    filter_upwards [he, hp, eventually_ge_atTop (1 : ℝ)] with x hx hxpow hx1
    have hx0 : 0 < x := by linarith
    have hpow : (x ^ τ) ^ (B / τ) = x ^ B := by
      rw [← Real.rpow_mul hx0.le]
      congr 1
      field_simp
    change 4 * B ≤ Real.exp (1 / (2 * B) * x ^ τ) / (x ^ τ) ^ (B / τ) at hx
    rw [hpow] at hx
    refine ⟨(le_div_iff₀ hB).mpr hxpow, ?_⟩
    have hh := (le_div_iff₀ (Real.rpow_pos_of_pos hx0 B)).mp hx
    convert hh using 1
    congr 1
    ring
  obtain ⟨R, hR⟩ := eventually_atTop.mp hall
  let Q := max R 1
  have hQ : 0 < Q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  refine ⟨Q⁻¹, inv_pos.mpr hQ, fun r hr hrr => ?_⟩
  have hx : Q ≤ r⁻¹ := by
    rw [← one_div, le_div_iff₀ hr]
    have hh : r * Q ≤ 1 := (le_div_iff₀ hQ).mp (by simpa only [one_div] using hrr)
    nlinarith
  have hh := hR r⁻¹ ((le_max_left _ _).trans hx)
  simpa only [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le] using hh

end Submission.Obl.k4_weighted_convex_tubes
