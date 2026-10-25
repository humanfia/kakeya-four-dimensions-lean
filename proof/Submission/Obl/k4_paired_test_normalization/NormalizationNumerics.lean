-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/NormalizationNumerics.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_paired_test_normalization

open Filter

/-- Fixed powers for the normalization step: the curvature cut, the two-role
sublevel deletion and the restored hidden-derivative floor. -/
theorem eventually_normalization_budgets {N : ℕ → ℝ} (hN : ∀ k, 0 < N k)
    (hNt : Tendsto N atTop atTop) {a : ℝ} (ha : 0 < a) (C V : ℝ) :
    ∀ᶠ k in atTop,
      1 ≤ N k ∧
      N k ^ (-(3 * a)) ≤ (N k ^ (-a)) ^ 2 / 2 ∧
      2 * N k ^ (-(29 * a)) ≤ (N k ^ (-a)) ^ 2 / 2 ∧
      1152 * C * N k ^ (-(25 * a)) <
        min (N k ^ (-(3 * a))) 1 * (N k ^ (-(10 * a))) ^ 2 ∧
      128 * V * N k ^ (-(10 * a)) ≤ N k ^ (-(9 * a)) ∧
      2 * (N k ^ a) ^ 2 * (128 * V * N k ^ (-(10 * a))) ≤ N k ^ (-(6 * a)) ∧
      2 * N k ^ (-(29 * a)) ≤ N k ^ (-(25 * a)) / 2 ∧
      N k ^ (-(26 * a)) ≤ N k ^ (-(25 * a)) / 2 ∧
      N k ^ (-(100 * a)) ≤ N k ^ (-(25 * a)) ∧
      (N k ^ (-(100 * a))) ^ 2 ≤ N k ^ (-(26 * a)) := by
  have hanchor := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -(3 * a) < -(2 * a) by linarith) 2
  have hraw := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -(29 * a) < -(2 * a) by linarith) 4
  have hsub := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -(25 * a) < -(23 * a) by linarith) (1152 * C)
  have hvol := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -(10 * a) < -(9 * a) by linarith) (128 * V)
  have hmass := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -(8 * a) < -(6 * a) by linarith) (256 * V)
  have hcross := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -(29 * a) < -(25 * a) by linarith) 4
  have hderiv := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -(26 * a) < -(25 * a) by linarith) 2
  filter_upwards [hNt.eventually (eventually_ge_atTop (1 : ℝ)), hanchor, hraw, hsub,
    hvol, hmass, hcross, hderiv] with k hk hanc hrawk hsubk hvolk hmassk hcrossk hderivk
  have hpow (b : ℝ) : (N k ^ b) ^ 2 = N k ^ (2 * b) := by
    rw [pow_two, ← Real.rpow_add (hN k)]
    congr 1
    ring
  have hsmall : N k ^ (-(3 * a)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hk (by linarith)
  have hanchorPow : (N k ^ (-a)) ^ 2 = N k ^ (-(2 * a)) := by
    rw [hpow]
    congr 1
    ring
  have hsubPow : min (N k ^ (-(3 * a))) 1 * (N k ^ (-(10 * a))) ^ 2 =
      N k ^ (-(23 * a)) := by
    rw [min_eq_left hsmall, hpow, ← Real.rpow_add (hN k)]
    congr 1
    ring
  have hmassPow : 2 * (N k ^ a) ^ 2 * (128 * V * N k ^ (-(10 * a))) =
      256 * V * N k ^ (-(8 * a)) := by
    rw [hpow]
    calc
      _ = 256 * V * (N k ^ (2 * a) * N k ^ (-(10 * a))) := by ring
      _ = _ := by rw [← Real.rpow_add (hN k)]; congr 2 <;> ring
  refine ⟨hk, ?_, ?_, ?_, hvolk.le, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hanchorPow]
    linarith
  · rw [hanchorPow]
    linarith
  · rwa [hsubPow]
  · rw [hmassPow]
    exact hmassk.le
  · linarith
  · linarith
  · exact Real.rpow_le_rpow_of_exponent_le hk (by linarith)
  · rw [hpow]
    exact Real.rpow_le_rpow_of_exponent_le hk (by linarith)

end Submission.Obl.k4_paired_test_normalization
