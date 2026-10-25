import Submission.Obl.k4_raw_localized_native_systems.C.OneSample

/-
Adapted from this LOT tree, o178, session x0596, `Asymptotics.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Asymptotic comparisons of powers of the scale

Along a sequence of scales tending to infinity, a constant multiple of a smaller
power is eventually below a larger power; the dyadic thickness `δ N u` lies between
`N^(-u)` and `2 N^(-u)`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- A constant times a smaller power is eventually below a larger power. -/
theorem eventually_const_mul_rpow_le {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) (C : ℝ)
    {a b : ℝ} (hab : a < b) : ∀ᶠ n in atTop, C * N n ^ a ≤ N n ^ b := by
  have hpow : Tendsto (fun n => N n ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hN
  filter_upwards [hpow.eventually_ge_atTop (max C 0), hN.eventually_gt_atTop 0] with n hn hpos
  have h1 : N n ^ b = N n ^ (b - a) * N n ^ a := by
    rw [← Real.rpow_add hpos]; ring_nf
  rw [h1]
  have ha : 0 ≤ N n ^ a := Real.rpow_nonneg hpos.le a
  calc C * N n ^ a ≤ max C 0 * N n ^ a := mul_le_mul_of_nonneg_right (le_max_left _ _) ha
    _ ≤ N n ^ (b - a) * N n ^ a := mul_le_mul_of_nonneg_right hn ha

/-- The dyadic thickness is at least the power. -/
theorem rpow_neg_le_delta {N u : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) : N ^ (-u) ≤ δ N u := by
  unfold δ
  have hN0 : 0 < N := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN
  set x := u * Real.log N / Real.log 2 with hx
  have hfl : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hNu : N ^ (-u) = (2 : ℝ) ^ (-x) := by
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hx]
    congr 1; field_simp
  rw [hNu, ← Real.rpow_intCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  linarith

/-- The dyadic thickness is at most twice the power. -/
theorem delta_le_two_rpow_neg {N u : ℝ} (hN : 1 ≤ N) : δ N u ≤ 2 * N ^ (-u) := by
  unfold δ
  have hN0 : 0 < N := by linarith
  set x := u * Real.log N / Real.log 2 with hx
  have hfl : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have hNu : N ^ (-u) = (2 : ℝ) ^ (-x) := by
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hx]
    have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    congr 1; field_simp
  rw [hNu, ← Real.rpow_intCast]
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (-x) = (2 : ℝ) ^ (1 - x) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_neg (by norm_num)]
    field_simp
  rw [h2]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  linarith

theorem delta_pos (N u : ℝ) : 0 < δ N u := by unfold δ; positivity

end

end Submission.Obl.k4_raw_localized_native_systems.C
