import Submission.Obl.k4_horizontal_supercritical_three_projections.Model
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Filter
open Submission.Obl.k4_profile_density_bounds

/-- One fixed coefficient exponent and arbitrarily small scalar output losses
pay for all physical return, reference and slicing errors. -/
theorem eventually_return_estimates_of_sequences (N K : ℕ → ℝ) (κ e₀ : ℝ)
    (hN₂ : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK₁ : ∀ k, 1 ≤ K k)
    (hKsub : ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, K k ≤ N k ^ ξ)
    (hκ₁ : κ ≤ 1) {s₀ s M τ ε : ℝ}
    (hs₀ : 0 < s₀) (he₀ : 100 * s₀ < e₀) (hM : 100 * s₀ < M)
    (hs : s < 3 * s₀ / 2) (hτ : 0 < τ) (hε : 0 < ε)
    (hτε : τ ≤ ε / 1000) (hτs : τ ≤ s₀ / 1000) (hτ₁ : τ ≤ 1 / 1000) :
    ∀ᶠ k in atTop,
      let N := N k
      let K := K k
      let D := N ^ (-(2 * κ * s₀))
      let χ := N ^ (-M)
      let E := N ^ (-e₀)
      let H := 10 * K
      let B := 240 * (N ^ τ) ^ 5
      χ ≤ D ∧ E + χ ≤ D ∧ H + 2 ≤ N ^ ε ∧ 150 * B ≤ N ^ ε ∧
      N ^ τ * N ^ (-s) + 16 * B * ((E + χ) / D) ≤ N ^ ε * N ^ (-s) ∧
      9 * B * ((1 + 4 * (H + 2)) / D) ^ 2 ≤ N ^ (10 + 8 * s₀) ∧
      4 * (N ^ τ) ^ 2 * K ≤ N ^ ε ∧
      N ^ (-ε) + (N ^ ε)⁻¹ * (4 * (N ^ τ) ^ 2 * K) ≤ N ^ (-2 * τ) := by
  let a := 2 * κ * s₀
  let L := min e₀ M
  have ha : a ≤ 2 * s₀ := by dsimp [a]; nlinarith [hκ₁]
  have hL : 100 * s₀ < L := lt_min he₀ hM
  have hN (k) : 1 ≤ N k := le_trans (by norm_num) (hN₂ k)
  have hcorner := eventually_subpower_mul_rpow_lt hN hNt hK₁ hKsub 1
    (show (0 : ℝ) < ε from hε) (show (0 : ℝ) ≤ 12 by norm_num)
  have hnorm := eventually_const_mul_rpow_lt hNt (show 5 * τ < ε by linarith) 36000
  have hround := eventually_const_mul_rpow_lt hNt (show -L < -a by linarith) 2
  have herror := eventually_const_mul_rpow_lt hNt
    (show 5 * τ + a - L < τ - s by linarith) 7680
  have hdouble := eventually_const_mul_rpow_lt hNt (show τ < ε by linarith) 2
  have hcoeff := eventually_subpower_mul_rpow_lt hN hNt hK₁ hKsub 2
    (show 5 * τ + 2 * a < 10 + 8 * s₀ by linarith) (show (0 : ℝ) ≤ 5186160 by norm_num)
  have hbudget := eventually_subpower_mul_rpow_lt hN hNt hK₁ hKsub 1
    (show 2 * τ < ε by linarith) (show (0 : ℝ) ≤ 4 by norm_num)
  have hlost := eventually_subpower_mul_rpow_lt hN hNt hK₁ hKsub 1
    (show -ε + 2 * τ < -2 * τ by linarith) (show (0 : ℝ) ≤ 8 by norm_num)
  filter_upwards [hcorner, hnorm, hround, herror, hdouble, hcoeff, hbudget, hlost]
    with k hcorner hnorm hround herror hdouble hcoeff hbudget hlost
  have hN₀ : 0 < N k := by linarith [hN k]
  have hK : 1 ≤ K k := hK₁ k
  simp only [pow_one, Real.rpow_zero, mul_one] at hcorner hbudget hlost
  have hE : N k ^ (-e₀) + N k ^ (-M) ≤ 2 * N k ^ (-L) := by
    have h₁ := Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg (min_le_left e₀ M))
    have h₂ := Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg (min_le_right e₀ M))
    dsimp [L] at *
    linarith
  have hpow5 : (N k ^ τ) ^ (5 : ℕ) = N k ^ (5 * τ) := by
    rw [← Real.rpow_mul_natCast hN₀.le]
    congr 1
    ring
  have hpow2 : (N k ^ τ) ^ (2 : ℕ) = N k ^ (2 * τ) := by
    rw [← Real.rpow_mul_natCast hN₀.le]
    congr 1
    ring
  have hinv : (N k ^ (-a))⁻¹ = N k ^ a := by rw [Real.rpow_neg hN₀.le a, inv_inv]
  have hχD : N k ^ (-M) ≤ N k ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
  refine ⟨hχD, hE.trans hround.le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · rw [hpow5]
    convert hnorm.le using 1; ring
  · have he : 16 * (240 * (N k ^ τ) ^ 5) *
        ((N k ^ (-e₀) + N k ^ (-M)) / N k ^ (-a)) ≤
        N k ^ τ * N k ^ (-s) := by
      calc
        _ ≤ 16 * (240 * (N k ^ τ) ^ 5) * ((2 * N k ^ (-L)) / N k ^ (-a)) := by
          gcongr
        _ = 7680 * N k ^ (5 * τ + a - L) := by
          rw [hpow5, div_eq_mul_inv, hinv]
          rw [Real.rpow_sub hN₀, Real.rpow_add hN₀, Real.rpow_neg hN₀.le L]
          ring
        _ ≤ N k ^ (τ - s) := herror.le
        _ = _ := by rw [Real.rpow_sub hN₀, Real.rpow_neg hN₀.le s]; ring
    have hd := mul_le_mul_of_nonneg_right hdouble.le (Real.rpow_nonneg hN₀.le (-s))
    linarith
  · have hcenter : 1 + 4 * (10 * K k + 2) ≤ 49 * K k := by linarith
    calc
      _ ≤ 9 * (240 * (N k ^ τ) ^ 5) * ((49 * K k) / N k ^ (-a)) ^ 2 := by
        gcongr
      _ = 5186160 * K k ^ 2 * N k ^ (5 * τ + 2 * a) := by
        have hpowA : N k ^ (2 * a) = (N k ^ a) ^ (2 : ℕ) := by
          rw [← Real.rpow_mul_natCast hN₀.le]
          congr 1
          ring
        rw [hpow5, div_eq_mul_inv, hinv, Real.rpow_add hN₀, hpowA]
        ring
      _ ≤ _ := hcoeff.le
  · simpa only [hpow2, mul_comm, mul_left_comm, mul_assoc] using hbudget.le
  · have hQ : 1 ≤ (N k ^ τ) ^ 2 := by
      have := Real.one_le_rpow (hN k) hτ.le
      nlinarith
    have hW : 1 ≤ 4 * (N k ^ τ) ^ 2 * K k := by nlinarith
    have hsmall : 2 * ((N k ^ ε)⁻¹ * (4 * (N k ^ τ) ^ 2 * K k)) ≤
        N k ^ (-2 * τ) := by
      calc
        _ = 8 * K k * N k ^ (-ε + 2 * τ) := by
          rw [hpow2, ← Real.rpow_neg hN₀.le ε, Real.rpow_add hN₀]
          ring
        _ ≤ _ := hlost.le
    have hfirst : N k ^ (-ε) ≤ (N k ^ ε)⁻¹ * (4 * (N k ^ τ) ^ 2 * K k) := by
      rw [Real.rpow_neg hN₀.le ε]
      exact le_mul_of_one_le_right (inv_nonneg.mpr (Real.rpow_nonneg hN₀.le ε)) hW
    linarith

/-- The sequence estimates specialized to the original horizontal model. -/
theorem eventually_return_estimates {α : Type} [MeasurableSpace α]
    (m : HorizontalModel α) (hm : m.Valid) {s₀ s M τ ε : ℝ}
    (hs₀ : 0 < s₀) (he₀ : 100 * s₀ < m.e₀) (hM : 100 * s₀ < M)
    (hs : s < 3 * s₀ / 2) (hτ : 0 < τ) (hε : 0 < ε)
    (hτε : τ ≤ ε / 1000) (hτs : τ ≤ s₀ / 1000) (hτ₁ : τ ≤ 1 / 1000) :
    ∀ᶠ k in atTop,
      let N := m.N k
      let K := m.K k
      let D := N ^ (-(2 * m.κ * s₀))
      let χ := N ^ (-M)
      let E := N ^ (-m.e₀)
      let H := 10 * K
      let B := 240 * (N ^ τ) ^ 5
      χ ≤ D ∧ E + χ ≤ D ∧ H + 2 ≤ N ^ ε ∧ 150 * B ≤ N ^ ε ∧
      N ^ τ * N ^ (-s) + 16 * B * ((E + χ) / D) ≤ N ^ ε * N ^ (-s) ∧
      9 * B * ((1 + 4 * (H + 2)) / D) ^ 2 ≤ N ^ (10 + 8 * s₀) ∧
      4 * (N ^ τ) ^ 2 * K ≤ N ^ ε ∧
      N ^ (-ε) + (N ^ ε)⁻¹ * (4 * (N ^ τ) ^ 2 * K) ≤ N ^ (-2 * τ) := by
  exact eventually_return_estimates_of_sequences m.N m.K m.κ m.e₀
    hm.N_ge hm.N_tendsto hm.K_ge hm.K_subpower hm.κ_le
    hs₀ he₀ hM hs hτ hε hτε hτs hτ₁

end Submission.Obl.k4_horizontal_supercritical_three_projections
