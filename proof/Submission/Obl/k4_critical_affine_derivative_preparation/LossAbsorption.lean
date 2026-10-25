import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_critical_affine_derivative_preparation

open Filter

/-- The scalar losses in physical Row recovery fit into every larger positive
output loss. The horizontal defect has a fixed power advantage. -/
theorem eventually_native_recovery_bounds
    {N K : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    {s e₀ δ ε : ℝ} (hs : 0 < s) (he₀ : 2 * s < e₀)
    (_hδ : 0 < δ) (hδε : δ < ε) :
    ∀ᶠ k in atTop,
      (1 + K k) * N k ^ δ ≤ N k ^ ε ∧
      ∀ (η H E defect : ℝ), η ≤ δ → 0 < H →
        H⁻¹ ≤ K k * N k ^ (s / 2) →
        0 ≤ E → E ≤ K k * N k ^ (-s) →
        0 ≤ defect → defect ≤ K k * N k ^ (-e₀) →
        N k ^ η * E + (1 + K k) * (N k ^ δ * E) + N k ^ δ * defect / H ≤
          N k ^ ε * N k ^ (-s) := by
  have hNone : ∀ k, 1 ≤ N k := fun k => le_trans (by norm_num) (hN k)
  have hfirst := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hNone hNt hK hsub 2 hδε (show (0 : ℝ) ≤ 8 by norm_num)
  have hsecond := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hNone hNt hK hsub 2
      (show δ - e₀ + s / 2 + s < ε by linarith)
      (show (0 : ℝ) ≤ 4 by norm_num)
  filter_upwards [hfirst, hsecond] with k hk₁ hk₂
  have hn : 0 < N k := by linarith [hN k]
  have hk : 0 < K k := by linarith [hK k]
  have hδpow : 0 < N k ^ δ := Real.rpow_pos_of_pos hn _
  have ha : 0 < N k ^ (-s) := Real.rpow_pos_of_pos hn _
  have hep : 0 < N k ^ ε := Real.rpow_pos_of_pos hn _
  have hKsq : K k ≤ K k ^ 2 := by nlinarith [hK k]
  have hcoeff : (1 + K k) * N k ^ δ ≤ N k ^ ε := by
    have h : 1 + K k ≤ 8 * K k ^ 2 := by nlinarith [hK k]
    exact (mul_le_mul_of_nonneg_right h hδpow.le).trans hk₁.le
  refine ⟨hcoeff, ?_⟩
  intro η H E defect hη hH hHinv hE hEhi hdef hdefhi
  have hηpow : N k ^ η ≤ N k ^ δ := Real.rpow_le_rpow_of_exponent_le (hNone k) hη
  have hE₁ : N k ^ η * E ≤ K k * N k ^ δ * N k ^ (-s) := by
    calc
      _ ≤ N k ^ δ * (K k * N k ^ (-s)) := mul_le_mul hηpow hEhi hE hδpow.le
      _ = _ := by ring
  have hE₂ : (1 + K k) * (N k ^ δ * E) ≤
      2 * K k ^ 2 * N k ^ δ * N k ^ (-s) := by
    calc
      _ ≤ (1 + K k) * (N k ^ δ * (K k * N k ^ (-s))) := by gcongr
      _ = ((1 + K k) * K k) * N k ^ δ * N k ^ (-s) := by ring
      _ ≤ _ := by
        have hm : (1 + K k) * K k ≤ 2 * K k ^ 2 := by nlinarith [hK k]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hm hδpow.le) ha.le
  have hE₃ : N k ^ δ * defect / H ≤ K k ^ 2 * N k ^ (δ - e₀ + s / 2) := by
    calc
      _ = N k ^ δ * defect * H⁻¹ := by ring
      _ ≤ N k ^ δ * (K k * N k ^ (-e₀)) * (K k * N k ^ (s / 2)) := by gcongr
      _ = _ := by
        rw [show δ - e₀ + s / 2 = δ + (-e₀) + s / 2 by ring,
          Real.rpow_add hn, Real.rpow_add hn]
        ring
  have hsmall₁ : 3 * K k ^ 2 * N k ^ δ * N k ^ (-s) <
      (N k ^ ε * N k ^ (-s)) / 2 := by
    have hm := mul_lt_mul_of_pos_right hk₁ ha
    nlinarith only [hm, mul_pos hep ha, mul_pos (sq_pos_of_pos hk) (mul_pos hδpow ha)]
  have hsmall₂ : K k ^ 2 * N k ^ (δ - e₀ + s / 2) <
      (N k ^ ε * N k ^ (-s)) / 2 := by
    have hm := mul_lt_mul_of_pos_right hk₂ ha
    rw [Real.rpow_add hn] at hm
    have hcancel : N k ^ s * N k ^ (-s) = 1 := by
      rw [← Real.rpow_add hn, add_neg_cancel, Real.rpow_zero]
    have hm' : 4 * K k ^ 2 * N k ^ (δ - e₀ + s / 2) < N k ^ ε * N k ^ (-s) := by
      simpa only [mul_assoc, hcancel, mul_one] using hm
    have hp : 0 ≤ K k ^ 2 * N k ^ (δ - e₀ + s / 2) := by positivity
    linarith
  have hmain : K k * N k ^ δ * N k ^ (-s) ≤ K k ^ 2 * N k ^ δ * N k ^ (-s) := by gcongr
  linarith

end Submission.Obl.k4_critical_affine_derivative_preparation
