import Submission.Obl.k4_horizon_chart_assembly.ParameterNumerics
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_horizon_chart_assembly

open Filter

/-- A scalar power error is eventually a small part of the original mass. -/
theorem eventually_atlas_scalar_error {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ k in atTop, N k ^ (-σ) ≤ (K k)⁻¹ / 8 := by
  have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 (show -σ < 0 by linarith) (by norm_num : (0 : ℝ) ≤ 8)
  filter_upwards [h] with k hk
  simp only [pow_one, Real.rpow_zero] at hk
  have hK₀ : 0 < K k := by linarith [hK k]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hK₀).2
  nlinarith

/-- The chart slack dominates all fixed multiples of the original subpower cap. -/
theorem eventually_atlas_slack {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, 256 * (K k + 2) ≤ N k ^ ε := by
  have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 hε (by norm_num : (0 : ℝ) ≤ 768)
  filter_upwards [h] with k hk
  simp only [pow_one, Real.rpow_zero, mul_one] at hk
  linarith [hK k]

/-- The coefficient left after summing the original heavy-cell tables tends
below one quarter, despite the fixed polynomial power of the subpower cap. -/
theorem eventually_atlas_residual_error {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {ε Cg : ℝ} (hε : 0 < ε) (hCg : 0 ≤ Cg) :
    ∀ᶠ k in atTop, 64 * Cg * K k ^ 5 * N k ^ (-ε / 2) ≤ 1 / 4 := by
  have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 5 (show -ε / 2 < 0 by linarith)
    (show 0 ≤ 256 * Cg by positivity)
  filter_upwards [h] with k hk
  simp only [Real.rpow_zero] at hk
  nlinarith

/-- The spatial and temporal cell volumes cancel exactly in the finite atlas
error, leaving a power loss covered by the tolerance exponent. -/
theorem atlas_residual_coefficient_le {N K D Cg ζ σ ε q n₀ upper : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hD : 0 ≤ D)
    (hCg : 0 ≤ Cg) (hζ : 0 ≤ ζ) (hq : 0 < q) (hn₀ : 0 < n₀)
    (hupper : D ≤ N ^ upper) (hgap : 2 * σ + upper * ζ ≤ ε / 2) :
    Cg * K ^ 3 * (4 * n₀ * ((2 * K + 2) * q) ^ 2 / N ^ ε) * D ^ ζ /
        (N ^ (-σ) * (n₀ * N ^ (-σ)) * q ^ 2) ≤
      64 * Cg * K ^ 5 * N ^ (-ε / 2) := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hK₀ : 0 ≤ K := by linarith
  have hratio := atlas_residual_ratio_le hN hD hupper hζ hgap
  have hcancel : Cg * K ^ 3 *
      (4 * n₀ * ((2 * K + 2) * q) ^ 2 / N ^ ε) * D ^ ζ /
        (N ^ (-σ) * (n₀ * N ^ (-σ)) * q ^ 2) =
      (4 * Cg * K ^ 3 * (2 * K + 2) ^ 2) *
        (N ^ σ * D ^ ζ / (N ^ (-σ) * N ^ ε)) := by
    rw [Real.rpow_neg hN₀.le]
    field_simp
    <;> ring
  have hR : (2 * K + 2) ^ 2 ≤ 16 * K ^ 2 := by nlinarith
  have hco : 4 * Cg * K ^ 3 * (2 * K + 2) ^ 2 ≤ 64 * Cg * K ^ 5 := by
    calc
      _ ≤ 4 * Cg * K ^ 3 * (16 * K ^ 2) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
      _ = _ := by ring
  rw [hcancel]
  exact (mul_le_mul_of_nonneg_left hratio (by positivity)).trans
    (mul_le_mul_of_nonneg_right hco (by positivity))

end Submission.Obl.k4_horizon_chart_assembly
