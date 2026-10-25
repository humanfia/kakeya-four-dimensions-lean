import Submission.Obl.k4_subcritical_chart_projection.ReturnEstimates
import Submission.Obl.k4_subcritical_chart_projection.ReturnAlgebra
import Submission.Obl.k4_profile_density_bounds.Asymptotics

set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

namespace Submission.Obl.k4_subcritical_chart_projection

open Filter
open Submission.Obl.k4_profile_density_bounds

/-- All physical-return estimates hold with one generous fixed coefficient
exponent. A small Scalar loss and any smaller chart loss absorb every constant. -/
theorem return_numerics_rule {α : Type} [MeasurableSpace α] (m : Model α)
    (hN : ∀ k, 2 ≤ m.N k) (hNt : Tendsto m.N atTop atTop)
    (hK : ∀ k, 1 ≤ m.K k)
    (hKsub : ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, m.K k ≤ m.N k ^ ξ)
    (hκ : 0 < m.κ) (hκ₁ : m.κ ≤ 1)
    {M s₀ depth : ℝ} (hs₀ : 0 < s₀) (hM : 100 * s₀ < M)
    (hnear : depth < 3 * s₀ / 2) :
    ReturnNumericsRule m M s₀ (100 + 100 * s₀) depth := by
  intro ε hε
  let τ := min (ε / 1000) (min (s₀ / 1000) (1 / 1000))
  have hτ : 0 < τ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hτε : τ ≤ ε / 1000 := min_le_left _ _
  have hτs : τ ≤ s₀ / 1000 := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₁ : τ ≤ 1 / 1000 := (min_le_right _ _).trans (min_le_right _ _)
  have hκs : m.κ * s₀ ≤ s₀ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hκ₁ hs₀.le
  have hN₁ : ∀ k, 1 ≤ m.N k := fun k => by linarith [hN k]
  have hfine := eventually_const_mul_rpow_lt hNt
    (show -M < -(2 * m.κ * s₀) by nlinarith) 2
  have hcorner := eventually_const_mul_rpow_lt hNt (show τ < ε by linarith) 6
  have hnorm := eventually_const_mul_rpow_lt hNt (show 5 * τ < ε by linarith) 36005
  have hfit₁ := eventually_const_mul_rpow_lt hNt (show τ - depth < ε - depth by linarith) 2
  have hfit₂ := eventually_const_mul_rpow_lt hNt
    (show 5 * τ - M + 2 * m.κ * s₀ < ε - depth by nlinarith) 15372
  have hcoeff := eventually_const_mul_rpow_lt hNt
    (show 9 * (τ + 2 * m.κ * s₀) < 100 + 100 * s₀ by nlinarith) 200000
  have hbudget := eventually_subpower_mul_rpow_lt hN₁ hNt hK hKsub 1
    (show 2 * τ < ε by linarith) (show (0 : ℝ) ≤ 4 by norm_num)
  have hremaining := eventually_subpower_mul_rpow_lt hN₁ hNt hK hKsub 1
    (show -ε + 2 * τ < -2 * τ by linarith) (show (0 : ℝ) ≤ 5 by norm_num)
  refine ⟨τ, hτ, τ, hτ, ?_⟩
  intro ξ hξ hξτ
  filter_upwards [hfine, hcorner, hnorm, hfit₁, hfit₂, hcoeff, hbudget, hremaining]
    with k hfine hcorner hnorm hfit₁ hfit₂ hcoeff hbudget hremaining
  let N := m.N k
  let Q := N ^ τ
  let H := N ^ ξ
  let D := N ^ (-(2 * m.κ * s₀))
  let A := N ^ (-s₀)
  let V := N ^ (-M)
  have hNk : 1 ≤ N := hN₁ k
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hNk
  have hQ : 1 ≤ Q := Real.one_le_rpow hNk hτ.le
  have hQ₀ : 0 ≤ Q := by linarith
  have hH₀ : 0 ≤ H := Real.rpow_nonneg hN₀.le _
  have hHQ : H ≤ Q := Real.rpow_le_rpow_of_exponent_le hNk hξτ
  have hD : 0 < D := Real.rpow_pos_of_pos hN₀ _
  have hD₁ : D ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNk (by nlinarith)
  have hA : 0 ≤ A := Real.rpow_nonneg hN₀.le _
  have hA₁ : A ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNk (by linarith)
  have hV : 0 < V := Real.rpow_pos_of_pos hN₀ _
  have hQpow (n : ℕ) : Q ^ n = N ^ ((n : ℝ) * τ) := by
    dsimp [Q]
    rw [← Real.rpow_mul_natCast hN₀.le]
    congr 1
    ring
  have hQ5 : Q ≤ Q ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hQ (by decide : 1 ≤ 5)
  have hHQ5 : H ≤ Q ^ 5 := hHQ.trans hQ5
  have hAQ5 : A * Q ^ 5 ≤ Q ^ 5 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA₁ (pow_nonneg hQ₀ 5)
  refine ⟨hfine.le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 3 * H + 3 ≤ N ^ ε
    apply le_trans (show 3 * H + 3 ≤ 6 * Q by linarith) hcorner.le
  · change 5 * H + A * (150 * (240 * Q ^ 5)) ≤ N ^ ε
    calc
      _ ≤ 36005 * Q ^ 5 := by nlinarith
      _ = 36005 * N ^ (5 * τ) := by rw [hQpow 5]; norm_num
      _ ≤ _ := hnorm.le
  · have hmain : A * (Q * N ^ (-(depth - s₀))) = N ^ (τ - depth) := by
      dsimp [A, Q]
      rw [← Real.rpow_add hN₀, ← Real.rpow_add hN₀]
      congr 1
      ring
    have hpert : A * (4 * (240 * Q ^ 5) * 4 * ((V + V) / D)) +
        (2 * H / D * V + 2 * H / D * (V + V)) ≤ 7686 * (Q ^ 5 * V / D) := by
      calc
        _ = (7680 * (A * Q ^ 5) + 6 * H) * (V / D) := by ring
        _ ≤ (7686 * Q ^ 5) * (V / D) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ = _ := by ring
    have hpertpow : Q ^ 5 * V / D = N ^ (5 * τ - M + 2 * m.κ * s₀) := by
      rw [hQpow 5]
      dsimp [V, D]
      rw [← Real.rpow_add hN₀, ← Real.rpow_sub hN₀]
      congr 1
      norm_num
      ring
    change A * (Q * N ^ (-(depth - s₀)) + 4 * (240 * Q ^ 5) * 4 * ((V + V) / D)) +
      (2 * H / D * V + 2 * H / D * (V + V)) ≤ N ^ ε * N ^ (-depth)
    calc
      _ = A * (Q * N ^ (-(depth - s₀))) +
          (A * (4 * (240 * Q ^ 5) * 4 * ((V + V) / D)) +
            (2 * H / D * V + 2 * H / D * (V + V))) := by ring
      _ ≤ N ^ (τ - depth) + 7686 * (Q ^ 5 * V / D) := add_le_add hmain.le hpert
      _ = N ^ (τ - depth) + 7686 * N ^ (5 * τ - M + 2 * m.κ * s₀) := by rw [hpertpow]
      _ ≤ N ^ (ε - depth) := by nlinarith only [hfit₁.le, hfit₂.le]
      _ = _ := by rw [← Real.rpow_add hN₀]; congr 1
  · let Z := Q / D
    have hZ : 1 ≤ Z := (le_div_iff₀ hD).mpr (by linarith)
    have hQZ : Q ≤ Z := (le_div_iff₀ hD).mpr (by nlinarith)
    have hHZ : H ≤ Z := hHQ.trans hQZ
    have hHD : H / D ≤ Z := div_le_div_of_nonneg_right hHQ hD.le
    have hDi : D⁻¹ ≤ Z := by
      rw [← one_div]
      exact div_le_div_of_nonneg_right hQ hD.le
    have hBZ : 240 * Q ^ 5 ≤ 240 * Z ^ 5 := by gcongr
    have he := return_coefficient_expression_le hD hH₀ hA hA₁
      (show 0 ≤ 240 * Q ^ 5 by positivity) hZ hHZ hHD hDi hBZ
    have hZeq : Z = N ^ (τ + 2 * m.κ * s₀) := by
      dsimp [Z, Q, D]
      rw [← Real.rpow_sub hN₀]
      congr 1
      ring
    have hZ9 : Z ^ (9 : ℕ) = N ^ (9 * (τ + 2 * m.κ * s₀)) := by
      rw [hZeq, ← Real.rpow_mul_natCast hN₀.le]
      congr 1
      norm_num
      ring
    apply he.trans
    rw [hZ9]
    exact hcoeff.le
  · change 4 * Q ^ 2 * m.K k ≤ N ^ ε
    calc
      _ = 4 * m.K k * N ^ (2 * τ) := by rw [hQpow 2]; norm_num; ring
      _ ≤ _ := by simpa only [pow_one] using hbudget.le
  · change N ^ (-ε) + (N ^ ε)⁻¹ * (4 * Q ^ 2 * m.K k) ≤ N ^ (-2 * τ)
    have hQK : 1 ≤ Q ^ 2 * m.K k :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ) (hK k)
    calc
      _ = (1 + 4 * Q ^ 2 * m.K k) * N ^ (-ε) := by rw [Real.rpow_neg hN₀.le]; ring
      _ ≤ (5 * Q ^ 2 * m.K k) * N ^ (-ε) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hN₀.le _)
      _ = 5 * m.K k * (Q ^ 2 * N ^ (-ε)) := by ring
      _ = 5 * m.K k * N ^ (-ε + 2 * τ) := by
        rw [hQpow 2, ← Real.rpow_add hN₀]
        congr 2
        norm_num
        ring
      _ ≤ _ := by simpa only [pow_one] using hremaining.le

end Submission.Obl.k4_subcritical_chart_projection
