import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- Convert the literal coarse/fine jet counts to the required loss.
The fine depth difference stays free, so the same index works for both
original projected colors. -/
theorem eventually_witness_card_budgets {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {d σ η ξ ε : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hσ : 0 ≤ σ) (hη : 0 < η) (hξ : 0 < ξ) (hση : σ < η)
    (hgap : σ + 20 * η + ξ < ε) :
    ∀ᶠ k in atTop, 160 * N k ^ σ ≤ N k ^ η ∧
      (∀ K : ℝ, 0 ≤ K → K ≤ N k ^ σ →
        14 * K * (N k ^ (20 * η) * (N k ^ ξ / (4 * N k ^ η)) ^ d) ≤ N k ^ ε) ∧
      (∀ s Δ : ℝ,
        N k ^ (20 * η) *
          (((16 * N k ^ η * N k ^ (-s) / N k ^ (-(s + Δ))) / (4 * N k ^ η))) ^ d ≤
            N k ^ ε * N k ^ (d * Δ)) ∧
      (∀ s Δ : ℝ, ξ ≤ Δ →
        N k ^ ξ ≤ 16 * N k ^ η * N k ^ (-s) / N k ^ (-(s + Δ))) := by
  have hcoarse : σ + 20 * η + ξ * d < ε := by
    nlinarith [mul_le_mul_of_nonneg_left hd1.le hξ.le]
  have hfine : 20 * η < ε := by linarith
  filter_upwards [hNt.eventually (eventually_const_mul_rpow_le 160 hση),
    hNt.eventually (eventually_const_mul_rpow_le 14 hcoarse),
    hNt.eventually (eventually_const_mul_rpow_le 4 hfine)] with k h160 hcoarsek hfinek
  have hNp : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hH : 1 ≤ N k ^ η := Real.one_le_rpow hN1 hη.le
  have hpow (a b : ℝ) : N k ^ a * N k ^ b = N k ^ (a + b) :=
    (Real.rpow_add hNp _ _).symm
  have hquot (s Δ : ℝ) : N k ^ (-s) / N k ^ (-(s + Δ)) = N k ^ Δ := by
    rw [← Real.rpow_sub hNp]
    congr 1
    ring
  refine ⟨h160, ?_, ?_, ?_⟩
  · intro K hK hKN
    have hratio : N k ^ ξ / (4 * N k ^ η) ≤ N k ^ ξ :=
      div_le_self (Real.rpow_pos_of_pos hNp _).le (by linarith)
    calc _ ≤ 14 * N k ^ σ * (N k ^ (20 * η) * (N k ^ ξ) ^ d) := by
          gcongr
      _ = 14 * ((N k ^ σ * N k ^ (20 * η)) * N k ^ (ξ * d)) := by
          rw [← Real.rpow_mul hNp.le]
          ring
      _ = 14 * N k ^ (σ + 20 * η + ξ * d) := by rw [hpow, hpow]
      _ ≤ _ := hcoarsek
  · intro s Δ
    have heq : (16 * N k ^ η * N k ^ (-s) / N k ^ (-(s + Δ))) /
        (4 * N k ^ η) = 4 * N k ^ Δ := by
      rw [mul_div_assoc, hquot]
      field_simp
      ring
    rw [heq, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity),
      ← Real.rpow_mul hNp.le]
    calc N k ^ (20 * η) * (4 ^ d * N k ^ (Δ * d))
        ≤ N k ^ (20 * η) * (4 * N k ^ (Δ * d)) := by
          gcongr
          exact Real.rpow_le_self_of_one_le (by norm_num) hd1.le
      _ = (4 * N k ^ (20 * η)) * N k ^ (d * Δ) := by rw [mul_comm Δ d]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfinek (by positivity)
  · intro s Δ hΔ
    rw [mul_div_assoc, hquot]
    calc N k ^ ξ ≤ N k ^ Δ := Real.rpow_le_rpow_of_exponent_le hN1 hΔ
      _ ≤ 16 * N k ^ η * N k ^ Δ := by nlinarith [Real.rpow_pos_of_pos hNp Δ]

end Submission.Obl.k4_wide_three_layer_scalar_inputs
