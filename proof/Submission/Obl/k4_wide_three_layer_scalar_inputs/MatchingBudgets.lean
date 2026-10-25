import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- Scalar budgets left after the geometric short-scale estimates.
The source floor is `N^(-10η)` and the matching constant is `N^(20η)`. -/
structure MatchingBudgets (N K d s₀ sp η ξ ηmatch R₀ Rc : ℝ) : Prop where
  coefficient_two : 2 ≤ N ^ (10 * s₀)
  match_two : 2 ≤ N ^ ξ
  graph_match : 2 * N ^ η ≤ N ^ ξ
  matching_cutoff : R₀ * (4 * N ^ η) ≤ N ^ ξ
  matching_gain : N ^ (20 * η) ≤ (N ^ ξ / (4 * N ^ η)) ^ ηmatch
  fit_resolution : 16 * N ^ (-sp) * N ^ η ≤ N ^ (-(sp - 2 * η))
  cap_budget : 24000 * K * (N ^ (-(sp - 2 * η))) ^ d ≤ N ^ (20 * η) * (N ^ (-sp)) ^ d
  horizon : -Real.logb N (18 * N ^ (-sp) * N ^ ξ) ≤ Rc
  jet_budget : N ^ (10 * η) * 12000 * K * (4 * N ^ η + 2) * 18 * (4 * N ^ η + 1) ≤
    N ^ (20 * η)

/-- These budgets hold uniformly in the earlier subpower constant.
Only strict power gaps are used; all exponents remain fixed before loss. -/
theorem eventually_matchingBudgets {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {d s₀ sp η ξ ηmatch R₀ Rc : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hξ : 0 < ξ) (hmatch : 0 < ηmatch)
    (hgain : 20 * η ≤ (ξ - 2 * η) * ηmatch) (hspRc : sp ≤ Rc) :
    ∀ᶠ k in atTop, ∀ K : ℝ, 1 ≤ K → K ≤ N k ^ η →
      MatchingBudgets (N k) K d s₀ sp η ξ ηmatch R₀ Rc := by
  have hξη : 2 * η < ξ := by nlinarith
  have hcapgap : η + (-(sp - 2 * η)) * d < 20 * η + (-sp) * d := by nlinarith
  have evB := hNt.eventually (eventually_const_mul_rpow_le 2
    (show (0 : ℝ) < 10 * s₀ by positivity))
  have evM := hNt.eventually (eventually_const_mul_rpow_le 2 hξ)
  have evR := hNt.eventually (eventually_const_mul_rpow_le (4 * R₀)
    (show η < ξ by linarith))
  have evδ := hNt.eventually (eventually_const_mul_rpow_le 4 (show η < 2 * η by linarith))
  have evfit := hNt.eventually (eventually_const_mul_rpow_le 16
    (show -sp + η < -(sp - 2 * η) by linarith))
  have evcap := hNt.eventually (eventually_const_mul_rpow_le 24000 hcapgap)
  have evjet := hNt.eventually (eventually_const_mul_rpow_le 6480000
    (show 13 * η < 20 * η by linarith))
  filter_upwards [evB, evM, evR, evδ, evfit, evcap, evjet] with k hB hM hR hδ hfit hcap hjet
  intro K hK hKH
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hNp : 0 < N k := by linarith [hN k]
  have hNgt : 1 < N k := by linarith [hN k]
  have hH : 1 ≤ N k ^ η := Real.one_le_rpow hN1 hη.le
  have hA : 0 < N k ^ (-sp) := Real.rpow_pos_of_pos hNp _
  have hM' : 2 ≤ N k ^ ξ := by simpa using hM
  have hδp : 0 < 4 * N k ^ η := by positivity
  have hδ' : 4 * N k ^ η ≤ N k ^ (2 * η) := hδ
  have hratio : N k ^ (ξ - 2 * η) ≤ N k ^ ξ / (4 * N k ^ η) := by
    rw [Real.rpow_sub hNp]
    exact div_le_div_of_nonneg_left (by positivity) hδp hδ'
  refine {
    coefficient_two := by simpa using hB
    match_two := hM'
    graph_match := ?_
    matching_cutoff := ?_
    matching_gain := ?_
    fit_resolution := ?_
    cap_budget := ?_
    horizon := ?_
    jet_budget := ?_ }
  · calc 2 * N k ^ η ≤ 4 * N k ^ η := by nlinarith
      _ ≤ N k ^ (2 * η) := hδ'
      _ ≤ N k ^ ξ := Real.rpow_le_rpow_of_exponent_le hN1 hξη.le
  · nlinarith only [hR]
  · calc N k ^ (20 * η) ≤ N k ^ ((ξ - 2 * η) * ηmatch) :=
          Real.rpow_le_rpow_of_exponent_le hN1 hgain
      _ = (N k ^ (ξ - 2 * η)) ^ ηmatch := Real.rpow_mul hNp.le _ _
      _ ≤ (N k ^ ξ / (4 * N k ^ η)) ^ ηmatch :=
          Real.rpow_le_rpow (by positivity) hratio hmatch.le
  · calc 16 * N k ^ (-sp) * N k ^ η = 16 * N k ^ (-sp + η) := by
          rw [mul_assoc, ← Real.rpow_add hNp]
      _ ≤ _ := hfit
  · calc 24000 * K * (N k ^ (-(sp - 2 * η))) ^ d
          ≤ 24000 * N k ^ η * (N k ^ (-(sp - 2 * η))) ^ d := by gcongr
      _ = 24000 * N k ^ (η + (-(sp - 2 * η)) * d) := by
          rw [← Real.rpow_mul hNp.le, mul_assoc, ← Real.rpow_add hNp]
      _ ≤ N k ^ (20 * η + (-sp) * d) := hcap
      _ = N k ^ (20 * η) * (N k ^ (-sp)) ^ d := by
          rw [Real.rpow_add hNp, Real.rpow_mul hNp.le (-sp) d]
  · have hlog := Real.logb_le_logb_of_le hNgt hA
        (show N k ^ (-sp) ≤ 18 * N k ^ (-sp) * N k ^ ξ by nlinarith only [hM', hA])
    rw [Real.logb_rpow hNp hNgt.ne'] at hlog
    linarith
  · calc N k ^ (10 * η) * 12000 * K * (4 * N k ^ η + 2) * 18 * (4 * N k ^ η + 1)
          ≤ N k ^ (10 * η) * 12000 * N k ^ η * (6 * N k ^ η) * 18 * (5 * N k ^ η) := by
            gcongr <;> linarith
      _ = 6480000 * (N k ^ (10 * η) * ((N k ^ η * N k ^ η) * N k ^ η)) := by ring
      _ = 6480000 * N k ^ (13 * η) := by
          rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
          congr 2
          ring
      _ ≤ _ := hjet

end Submission.Obl.k4_wide_three_layer_scalar_inputs
