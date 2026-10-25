import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Submission.Obl.k4_subcritical_chart_projection

open Filter

/-- Every loss used before calling Scalar, including the two original-law
mass budgets, at one index. -/
structure InputEstimates (N K κ s₀ depth M ξ η τ cut η₀ : ℝ) : Prop where
  large : 2 ≤ N ^ ξ
  K_le : K ≤ N ^ ξ
  K_eta : K ≤ N ^ η
  coefficient : 2 * N ^ ξ ≤ N ^ η
  pure : 8 * 10 ^ 6 * (N ^ ξ) ^ 3 * K ≤ N ^ η
  whole : 2 * 10 ^ 6 * (N ^ ξ) ^ 5 * K ≤ N ^ (10 * ξ)
  mesh : N ^ (-M) ≤ N ^ (-(2 * κ * s₀)) * N ^ (-(20 * s₀))
  mesh_square : N ^ (-M) ≤ N ^ (-(2 * κ * s₀)) * (N ^ (-(20 * s₀))) ^ 2
  variation : 24 * (N ^ ξ) ^ 2 * N ^ (-M) / N ^ (-(2 * κ * s₀)) ≤ N ^ (-depth)
  xi_half : 2 * ξ ≤ s₀
  cut_eta : cut ≤ η
  ten_xi_eta : 10 * ξ ≤ η
  ratio_one : cut + 10 * ξ ≤ 1
  support_budget : cut + 20 * ξ ≤ η
  prune : N ^ (-cut) * (1 + N ^ ξ * K) ≤ N ^ (-η₀) / 2
  success : N ^ (-2 * τ) ≤ (N ^ (-τ) / K) * (N ^ (-η₀) / 2)

private theorem input_estimates_of_large {N K κ s₀ depth M ξ η τ cut η₀ : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hs₀ : 0 < s₀)
    (hdepth : depth < 3 * s₀ / 2) (hM : 100 * s₀ < M)
    (hξ : 0 < ξ) (hξcut : ξ ≤ cut / 1000) (hξs : ξ ≤ s₀ / 100)
    (hcutη : cut ≤ η / 10) (hcut₁ : cut ≤ 1 / 10)
    (hlarge : 8 * 10 ^ 6 ≤ N ^ ξ) (hKξ : K ≤ N ^ ξ)
    (hprune : 4 * N ^ (-cut + 2 * ξ) ≤ N ^ (-η₀))
    (hsuccess : 2 * K ≤ N ^ (τ - η₀)) :
    InputEstimates N K κ s₀ depth M ξ η τ cut η₀ := by
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hK₀ : 0 < K := by linarith
  have hH : 1 ≤ N ^ ξ := Real.one_le_rpow hN hξ.le
  have hH₀ : 0 ≤ N ^ ξ := by positivity
  have hpow (n : ℕ) : (N ^ ξ) ^ n = N ^ (ξ * n) :=
    (Real.rpow_mul_natCast hN₀.le ξ n).symm
  have hcoeff : 2 * N ^ ξ ≤ N ^ η := by
    calc
      _ ≤ (N ^ ξ) ^ 2 := by nlinarith
      _ = N ^ (ξ * 2) := hpow 2
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hpure : 8 * 10 ^ 6 * (N ^ ξ) ^ 3 * K ≤ N ^ η := by
    calc
      _ ≤ (N ^ ξ) * (N ^ ξ) ^ 3 * (N ^ ξ) := by gcongr
      _ = (N ^ ξ) ^ 5 := by ring
      _ = N ^ (ξ * 5) := hpow 5
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hwhole : 2 * 10 ^ 6 * (N ^ ξ) ^ 5 * K ≤ N ^ (10 * ξ) := by
    calc
      _ ≤ (N ^ ξ) * (N ^ ξ) ^ 5 * (N ^ ξ) := by
        gcongr
        linarith
      _ = (N ^ ξ) ^ 7 := by ring
      _ = N ^ (ξ * 7) := hpow 7
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hmesh₂ : N ^ (-M) ≤ N ^ (-(2 * κ * s₀)) * (N ^ (-(20 * s₀))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hN₀.le, ← Real.rpow_add hN₀]
    apply Real.rpow_le_rpow_of_exponent_le hN
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_right hκ₁ hs₀.le]
  have hmesh : N ^ (-M) ≤ N ^ (-(2 * κ * s₀)) * N ^ (-(20 * s₀)) := by
    rw [← Real.rpow_add hN₀]
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith
  have hvar : 24 * (N ^ ξ) ^ 2 * N ^ (-M) / N ^ (-(2 * κ * s₀)) ≤ N ^ (-depth) := by
    calc
      _ ≤ (N ^ ξ) ^ 3 * N ^ (-M) / N ^ (-(2 * κ * s₀)) := by
        gcongr
        nlinarith
      _ = N ^ (ξ * 3 - M + 2 * κ * s₀) := by
        rw [hpow 3, ← Real.rpow_add hN₀, ← Real.rpow_sub hN₀]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  have hprune' : N ^ (-cut) * (1 + N ^ ξ * K) ≤ N ^ (-η₀) / 2 := by
    calc
      _ ≤ N ^ (-cut) * (2 * (N ^ ξ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left hKξ hH₀]
      _ = 2 * N ^ (-cut) * (N ^ ξ) ^ 2 := by ring
      _ = 2 * N ^ (-cut + 2 * ξ) := by
        rw [hpow 2, mul_assoc, ← Real.rpow_add hN₀]
        congr 2
        ring
      _ ≤ _ := by linarith
  have hsuccess' : N ^ (-2 * τ) ≤ (N ^ (-τ) / K) * (N ^ (-η₀) / 2) := by
    have hmul : 2 * K * N ^ (-2 * τ) ≤ N ^ (-τ - η₀) := by
      calc
        _ ≤ N ^ (τ - η₀) * N ^ (-2 * τ) :=
          mul_le_mul_of_nonneg_right hsuccess (by positivity)
        _ = _ := by rw [← Real.rpow_add hN₀]; congr 1; ring
    calc
      _ ≤ N ^ (-τ - η₀) / (2 * K) := (le_div_iff₀ (by positivity)).mpr (by
        simpa only [mul_comm] using hmul)
      _ = _ := by
        rw [show -τ - η₀ = -τ + -η₀ by ring, Real.rpow_add hN₀]
        field_simp
  refine ⟨by linarith, hKξ, hKξ.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    hcoeff, hpure, hwhole, hmesh, hmesh₂, hvar, by linarith, by linarith,
    by linarith, by linarith, by linarith, hprune', hsuccess'⟩

/-- Choose the input cutoff and maximum chart loss after Scalar has fixed
its positive admissibility loss. The quantifier over all smaller chart losses
allows the three Scalar calls to use one common corrected chart system. -/
theorem exists_input_exponents (N K : ℕ → ℝ)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hKsub : ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, K k ≤ N k ^ ξ)
    {κ s₀ depth M η τ : ℝ} (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hs₀ : 0 < s₀)
    (hdepth : depth < 3 * s₀ / 2) (hM : 100 * s₀ < M)
    (hη : 0 < η) (hτ : 0 < τ) :
    ∃ cut η₀ ξ₀ : ℝ, 0 < cut ∧ 0 < η₀ ∧ 0 < ξ₀ ∧
      ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ᶠ k in atTop,
        InputEstimates (N k) (K k) κ s₀ depth M ξ η τ cut η₀ := by
  let cut := min (η / 10) (min (τ / 10) (1 / 10))
  let η₀ := cut / 100
  let ξ₀ := min (cut / 1000) (s₀ / 100)
  have hcut : 0 < cut := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hcutη : cut ≤ η / 10 := min_le_left _ _
  have hcutτ : cut ≤ τ / 10 := (min_le_right _ _).trans (min_le_left _ _)
  have hcut₁ : cut ≤ 1 / 10 := (min_le_right _ _).trans (min_le_right _ _)
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hξ₀ : 0 < ξ₀ := lt_min (by positivity) (by positivity)
  refine ⟨cut, η₀, ξ₀, hcut, hη₀, hξ₀, ?_⟩
  intro ξ hξ hξ₀'
  have hξcut : ξ ≤ cut / 1000 := hξ₀'.trans (min_le_left _ _)
  have hξs : ξ ≤ s₀ / 100 := hξ₀'.trans (min_le_right _ _)
  have hprune := hNt.eventually
    (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 4
      (show -cut + 2 * ξ < -η₀ by dsimp [η₀]; linarith))
  have hsuccess := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [hN k] : ∀ k, 1 ≤ N k) hNt hK hKsub 1
    (show (0 : ℝ) < τ - η₀ by dsimp [η₀]; linarith) (show (0 : ℝ) ≤ 2 by norm_num)
  have hlarge : ∀ᶠ k in atTop, 8 * 10 ^ 6 ≤ N k ^ ξ :=
    ((tendsto_rpow_atTop hξ).comp hNt).eventually_ge_atTop _
  filter_upwards [hKsub ξ hξ, hprune, hsuccess, hlarge] with k hKξ hprune hsuccess hlarge
  apply input_estimates_of_large (by linarith [hN k]) (hK k) hκ hκ₁ hs₀
    hdepth hM hξ hξcut hξs hcutη hcut₁ hlarge hKξ hprune
  simpa only [pow_one, Real.rpow_zero, mul_one] using hsuccess.le

end Submission.Obl.k4_subcritical_chart_projection
