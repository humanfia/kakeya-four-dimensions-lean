import Mathlib

open Filter

namespace Submission.Obl.k4_scalar_profile_raw_certification

/-- The noise factor written as one power of the ambient scale. -/
lemma noise_factor_eq {N : ℝ} (hN : 1 ≤ N) (m u : ℝ) :
    min 1 (N ^ (m - u)) = N ^ (-max 0 (u - m)) := by
  by_cases h : u ≤ m
  · rw [max_eq_left (by linarith), neg_zero, Real.rpow_zero,
      min_eq_left (Real.one_le_rpow hN (by linarith))]
  · have hu : m ≤ u := (lt_of_not_ge h).le
    rw [max_eq_right (by linarith),
      min_eq_right (Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith))]
    congr 1
    ring

/-- Multiplying by a subpower loss adds no limiting exponent. -/
lemma eventually_mul_power_le {N K c : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hK : ∀ k, 0 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {C₀ : ℝ}
    (hc : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, c k ≤ N k ^ (C₀ + ε))
    (a ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, K k * c k * N k ^ a ≤ N k ^ (C₀ + a + ε) := by
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [hsub (ε / 2) hε2, hc (ε / 2) hε2] with k hk hck
  have hkN : 0 < N k := by linarith [hN k]
  calc
    K k * c k * N k ^ a ≤ K k * N k ^ (C₀ + ε / 2) * N k ^ a := by
      gcongr
      exact hK k
    _ ≤ N k ^ (ε / 2) * N k ^ (C₀ + ε / 2) * N k ^ a := by gcongr
    _ = N k ^ (C₀ + a + ε) := by
      rw [← Real.rpow_add hkN, ← Real.rpow_add hkN]
      congr 1
      ring

/-- The lower power bound on a coefficient is the upper power bound on its inverse. -/
lemma eventually_inv_le {N c : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    {C₀ : ℝ}
    (hc : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, N k ^ (C₀ - ε) ≤ c k)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, (c k)⁻¹ ≤ N k ^ (-C₀ + ε) := by
  filter_upwards [hc ε hε] with k hk
  have hkN : 0 < N k := by linarith [hN k]
  have hp : 0 < N k ^ (C₀ - ε) := Real.rpow_pos_of_pos hkN _
  calc
    (c k)⁻¹ ≤ (N k ^ (C₀ - ε))⁻¹ := inv_anti₀ hp hk
    _ = N k ^ (-C₀ + ε) := by rw [← Real.rpow_neg hkN.le]; congr 1; ring

end Submission.Obl.k4_scalar_profile_raw_certification
