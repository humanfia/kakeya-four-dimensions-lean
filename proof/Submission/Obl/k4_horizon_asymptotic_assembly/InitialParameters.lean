/- Adapted from this LOT tree, obligation o103, session x0354, commit162b3a6,
Submission/Obl/k4_initial_horizon_bound/InitialParameters.lean.
Named forms and Boolean calculus originally came from o103/x0360, commits642b39c andb0c6023;
the finite interface definitions came from o160/x0559/b0539eb, as attributed below. -/

import Mathlib
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! Choose the plank loss before its returned duration exponent, then choose
the duration cut. This avoids a circular dependence between these two losses. -/

namespace Submission.Obl.k4_horizon_asymptotic_assembly

theorem initial_plank_loss_choice {ε A : ℝ} (hε : 0 < ε) (hA : 0 < A) :
    ∃ θ : ℝ, 0 < θ ∧ A * θ ≤ ε / 100 ∧ ∀ η : ℝ, 0 < η →
      ∃ σ : ℝ, 0 < σ ∧ σ ≤ A * η ∧ σ ≤ ε / 100 ∧
        2 * σ + A * θ ≤ ε / 10 := by
  let θ := ε / (100 * A)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have heq : A * θ = ε / 100 := by dsimp [θ]; field_simp
  refine ⟨θ, hθ, heq.le, ?_⟩
  intro η hη
  let σ := min (A * η / 2) (ε / 100)
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  have hσ₁ : σ ≤ A * η / 2 := min_le_left _ _
  have hσ₂ : σ ≤ ε / 100 := min_le_right _ _
  refine ⟨σ, hσ, ?_, hσ₂, ?_⟩
  · have : 0 < A * η := mul_pos hA hη
    linarith
  · rw [heq]
    linarith

theorem mesh_duration_power_le {N D A η σ : ℝ} (hN : 1 ≤ N)
    (hmesh : N ^ A ≤ D) (hη : 0 < η) (hσ : σ ≤ A * η) :
    D ^ (-η) ≤ N ^ (-σ) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  calc
    _ ≤ (N ^ A) ^ (-η) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNpos A) hmesh (by linarith)
    _ = N ^ (-(A * η)) := by rw [← Real.rpow_mul hNpos.le]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- After cancelling the physical cell volume, the analytic support-table
error has this ratio. A fixed fraction of the requested slack exponent pays
for the duration and typical-density losses simultaneously. -/
theorem initial_residual_ratio_le {N D A θ σ ε : ℝ} (hN : 1 ≤ N)
    (hD : 0 ≤ D) (hupper : D ≤ N ^ A) (hθ : 0 ≤ θ)
    (hgap : 2 * σ + A * θ ≤ ε / 2) :
    N ^ σ * D ^ θ / (N ^ (-σ) * N ^ ε) ≤ N ^ (-ε / 2) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hpow : D ^ θ ≤ N ^ (A * θ) := by
    rw [Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow hD hupper hθ
  calc
    _ ≤ N ^ σ * N ^ (A * θ) / (N ^ (-σ) * N ^ ε) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (by positivity)
    _ = N ^ (2 * σ + A * θ - ε) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_sub hNpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The simpler relative-mass duration cut also works: every fixed positive
plank exponent eventually permits `s = 1 / (16 K)`. The exponent affects only
the starting sample, so no power parameter has to depend on it. -/
theorem eventually_core_duration_threshold {N K D : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε)
    {A η : ℝ} (hA : 0 < A) (hη : 0 < η)
    (hmesh : ∀ᶠ k in Filter.atTop, N k ^ A ≤ D k) :
    ∀ᶠ k in Filter.atTop, D k ^ (-η) ≤ (16 * K k)⁻¹ := by
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 1 (show -(A * η) < 0 by nlinarith) (show (0 : ℝ) ≤ 16 by norm_num)
  filter_upwards [hsmall, hmesh] with k hk hD
  have hlong := mesh_duration_power_le (hN k) hD hη (le_refl (A * η))
  have hKpos : 0 < K k := zero_lt_one.trans_le (hK k)
  rw [← one_div]
  apply (le_div_iff₀ (mul_pos (by norm_num) hKpos)).mpr
  calc
    _ ≤ N k ^ (-(A * η)) * (16 * K k) :=
      mul_le_mul_of_nonneg_right hlong (by positivity)
    _ ≤ 1 := by simpa only [pow_one, Real.rpow_zero, mul_comm] using hk.le

end Submission.Obl.k4_horizon_asymptotic_assembly
