import Submission.Obl.k4_horizontal_supercritical_three_projections.ReturnNumerics

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Filter
open Submission.Obl.k4_profile_density_bounds

/-- Choose the chart cutoff and original cap loss after the scalar input
loss is known. The retained chart mass still pays for the entire scalar ensemble. -/
theorem exists_chart_selection_exponents (N K : ℕ → ℝ)
    (hN₂ : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK₁ : ∀ k, 1 ≤ K k)
    (hKsub : ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, K k ≤ N k ^ ξ)
    {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ b ξ η₀ : ℝ, 0 < b ∧ 0 < ξ ∧ 0 < η₀ ∧ b ≤ η ∧ ξ ≤ η ∧
      b + ξ ≤ 1 ∧ b + 2 * ξ ≤ η ∧
      ∀ᶠ k in atTop,
        K k ≤ N k ^ ξ ∧ 10 * K k ≤ N k ^ η ∧
        N k ^ (-b) * (1 + 441 * (K k) ^ 2) ≤ N k ^ (-η₀) / 2 ∧
        N k ^ (-2 * τ) ≤ (N k ^ (-τ) / K k) * (N k ^ (-η₀) / 2) := by
  let b := min (η / 10) (min (τ / 10) (1 / 10))
  let ξ := b / 10
  let η₀ := b / 100
  have hb : 0 < b := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hbη : b ≤ η / 10 := min_le_left _ _
  have hbτ : b ≤ τ / 10 := (min_le_right _ _).trans (min_le_left _ _)
  have hb₁ : b ≤ 1 / 10 := (min_le_right _ _).trans (min_le_right _ _)
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hη₀b : η₀ < b := by dsimp [η₀]; linarith
  have hη₀τ : η₀ < τ := by dsimp [η₀]; linarith
  have hN (k) : 1 ≤ N k := by linarith [hN₂ k]
  have hcoeff := eventually_subpower_mul_rpow_lt hN hNt hK₁ hKsub 1 hη
    (show (0 : ℝ) ≤ 10 by norm_num)
  have hprune := eventually_subpower_mul_rpow_lt hN hNt hK₁ hKsub 2
    (show -b < -η₀ by linarith) (show (0 : ℝ) ≤ 884 by norm_num)
  have hsuccess := eventually_subpower_mul_rpow_lt hN hNt hK₁ hKsub 1
    (show (0 : ℝ) < τ - η₀ by linarith) (show (0 : ℝ) ≤ 2 by norm_num)
  refine ⟨b, ξ, η₀, hb, hξ, hη₀, by linarith, by dsimp [ξ]; linarith,
    by dsimp [ξ]; linarith, by dsimp [ξ]; linarith, ?_⟩
  filter_upwards [hKsub ξ hξ, hcoeff, hprune, hsuccess] with k hK hcoeff hprune hsuccess
  simp only [pow_one, Real.rpow_zero, mul_one] at hcoeff hsuccess
  have hN₀ : 0 < N k := by linarith [hN k]
  have hK₀ : 0 < K k := by linarith [hK₁ k]
  refine ⟨hK, hcoeff.le, ?_, ?_⟩
  · have hKsq : 1 ≤ (K k) ^ 2 := one_le_pow₀ (hK₁ k)
    calc
      _ ≤ 442 * (K k) ^ 2 * N k ^ (-b) := by
        nlinarith [Real.rpow_nonneg hN₀.le (-b)]
      _ ≤ _ := by linarith [hprune.le]
  · have hmul : 2 * K k * N k ^ (-2 * τ) ≤ N k ^ (-τ - η₀) := by
      calc
        _ ≤ N k ^ (τ - η₀) * N k ^ (-2 * τ) :=
          mul_le_mul_of_nonneg_right hsuccess.le (Real.rpow_nonneg hN₀.le _)
        _ = _ := by rw [← Real.rpow_add hN₀]; congr 1; ring
    calc
      _ ≤ N k ^ (-τ - η₀) / (2 * K k) := (le_div_iff₀ (by positivity)).mpr (by
        simpa only [mul_comm] using hmul)
      _ = _ := by
        rw [show -τ - η₀ = -τ + -η₀ by ring, Real.rpow_add hN₀]
        field_simp


/-- The simultaneous active cutoffs give exactly the scalar density range,
input mass and reciprocal-prefactor budget needed by normalized admissibility. -/
theorem active_chart_scalar_bounds {N K b ξ η c : ℝ} (hN : 1 ≤ N)
    (hK : K ≤ N ^ ξ) (hbη : b ≤ η) (hξη : ξ ≤ η)
    (hbξ : b + ξ ≤ 1) (hbudget : b + 2 * ξ ≤ η)
    (hc₁ : N ^ (-b) / N ^ ξ ≤ c) (hc₂ : c ≤ K / N ^ (-b)) :
    0 < c ∧ N ^ (-(1 : ℝ)) ≤ c ∧ c ≤ N ^ (1 : ℝ) ∧
      N ^ (-η) ≤ N ^ (-b) ∧ N ^ ξ ≤ N ^ η ∧ N ^ ξ ≤ N ^ η * c⁻¹ := by
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hc : 0 < c := lt_of_lt_of_le (by positivity : 0 < N ^ (-b) / N ^ ξ) hc₁
  have hlo : N ^ (-b - ξ) ≤ c := by
    simpa only [Real.rpow_sub hN₀] using hc₁
  have hup : c ≤ N ^ (b + ξ) := by
    calc
      c ≤ K / N ^ (-b) := hc₂
      _ ≤ N ^ ξ / N ^ (-b) := div_le_div_of_nonneg_right hK (Real.rpow_nonneg hN₀.le _)
      _ = _ := by
        rw [← Real.rpow_sub hN₀]
        congr 1
        ring
  refine ⟨hc, ?_, hup.trans (Real.rpow_le_rpow_of_exponent_le hN hbξ),
    Real.rpow_le_rpow_of_exponent_le hN (by linarith),
    Real.rpow_le_rpow_of_exponent_le hN hξη, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith : -(1 : ℝ) ≤ -b - ξ)).trans hlo
  · have hmul : N ^ ξ * c ≤ N ^ η := by
      calc
        _ ≤ N ^ ξ * N ^ (b + ξ) := mul_le_mul_of_nonneg_left hup (Real.rpow_nonneg hN₀.le _)
        _ = N ^ (b + 2 * ξ) := by
          rw [← Real.rpow_add hN₀]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hbudget
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hc).mpr hmul

end Submission.Obl.k4_horizontal_supercritical_three_projections
