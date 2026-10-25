import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter Finset
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- The actual two reference tables pay for the common restriction.
The input loss is smaller than the comparison loss, and matching has a
fixed strict gain before either loss is chosen. -/
theorem eventually_short_comparison_loss {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {σ η ξ ηmatch : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (hση : 100 * σ ≤ η) (hmatch : 0 < ηmatch)
    (hgain : 50 * η ≤ (ξ - 2 * η) * ηmatch) :
    ∀ᶠ k in atTop, ∀ (K b : ℝ) (p : Fin 3 → ℝ),
      1 ≤ K → K ≤ N k ^ σ → 0 ≤ b → b ≤ 140 * K ^ 3 →
      (∀ h, 0 ≤ p h) → (∀ h, p h ≤ 6 * N k ^ (2 * σ)) →
      b / N k ^ (10 * η) + (∑ h, p h / N k ^ (10 * η)) +
        N k ^ (20 * η) * (N k ^ ξ / (4 * N k ^ η)) ^ (-ηmatch) * (b + p 0) ≤
          N k ^ (-η) ∧
      N k ^ (-η) + N k ^ (-η) ≤ N k ^ (-σ) := by
  have hlight : 3 * σ - 10 * η < -η := by linarith
  have hfar : 20 * η + 3 * σ - (ξ - 2 * η) * ηmatch < -η := by linarith
  filter_upwards [hNt.eventually (eventually_const_mul_rpow_le 316 hlight),
    hNt.eventually (eventually_const_mul_rpow_le 292 hfar),
    hNt.eventually (eventually_const_mul_rpow_le 4 (show η < 2 * η by linarith)),
    hNt.eventually (eventually_const_mul_rpow_le 2 (show -η < -σ by linarith))]
      with k hlightk hfark hδk hmassk
  intro K b p hK hKN hb hbK hp hpN
  have hNp : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hpow (a b : ℝ) : N k ^ a * N k ^ b = N k ^ (a + b) :=
    (Real.rpow_add hNp _ _).symm
  have hKN3 : K ^ 3 ≤ N k ^ (3 * σ) := by
    calc K ^ 3 ≤ (N k ^ σ) ^ 3 := pow_le_pow_left₀ (by linarith) hKN 3
      _ = _ := by rw [← Real.rpow_mul_natCast hNp.le]; congr 1; ring
  have hbN : b ≤ 140 * N k ^ (3 * σ) :=
    hbK.trans (mul_le_mul_of_nonneg_left hKN3 (by norm_num))
  have hpN' : ∀ h, p h ≤ 6 * N k ^ (3 * σ) := fun h =>
    (hpN h).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num))
  have hpSum : (∑ h, p h) ≤ 18 * N k ^ (3 * σ) := by
    calc (∑ h, p h) ≤ ∑ _h : Fin 3, 6 * N k ^ (3 * σ) :=
          Finset.sum_le_sum fun h _ => hpN' h
      _ = _ := by simp; ring
  have hlightbd : b / N k ^ (10 * η) + (∑ h, p h / N k ^ (10 * η)) ≤
      158 * N k ^ (3 * σ - 10 * η) := by
    rw [← Finset.sum_div, ← add_div, Real.rpow_sub hNp, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hratio : N k ^ (ξ - 2 * η) ≤ N k ^ ξ / (4 * N k ^ η) := by
    rw [Real.rpow_sub hNp]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hδk
  have hneg : (N k ^ ξ / (4 * N k ^ η)) ^ (-ηmatch) ≤
      N k ^ (-(ξ - 2 * η) * ηmatch) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hNp _) hratio
      (by linarith : -ηmatch ≤ 0)
    rw [← Real.rpow_mul hNp.le] at hh
    convert hh using 1 <;> congr 1 <;> ring
  have hfarbd : N k ^ (20 * η) * (N k ^ ξ / (4 * N k ^ η)) ^ (-ηmatch) * (b + p 0) ≤
      146 * N k ^ (20 * η + 3 * σ - (ξ - 2 * η) * ηmatch) := by
    calc _ ≤ N k ^ (20 * η) * N k ^ (-(ξ - 2 * η) * ηmatch) *
          (146 * N k ^ (3 * σ)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hneg (by positivity)
            · linarith [hpN' 0]
            · exact add_nonneg hb (hp 0)
            · positivity
      _ = 146 * ((N k ^ (20 * η) * N k ^ (-(ξ - 2 * η) * ηmatch)) *
          N k ^ (3 * σ)) := by ring
      _ = _ := by rw [hpow, hpow]; congr 2; ring
  constructor
  · linarith
  · linarith

end Submission.Obl.k4_wide_three_layer_scalar_inputs
