/-
Adapted from: here:o204
Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeTimeRatio.lean.
Any earlier attribution is retained below.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The original dyadic time bounds resolve the fine anchor at the actual
second strip radius. This estimate is uniform over every original packet. -/

namespace Submission.Lib.K4NativePreparationNumerics

theorem native_time_ratio_of_scale_bounds {N κ₁ sOld sFine δ₀ L : ℝ}
    {Told Tfine : ℕ} (hN : 0 < N)
    (hOld : (2 : ℝ) ^ Told ≤ N ^ ((κ₁ * sOld + δ₀) * L))
    (hFine : N ^ ((κ₁ * sFine - δ₀) * L) ≤ (2 : ℝ) ^ Tfine) :
    N ^ (2 * δ₀ * L) * ((2 : ℝ) ^ Told / (2 : ℝ) ^ Tfine) ≤
      N ^ ((-κ₁ * (sFine - sOld) + 4 * δ₀) * L) := by
  calc
    _ ≤ N ^ (2 * δ₀ * L) *
        (N ^ ((κ₁ * sOld + δ₀) * L) / N ^ ((κ₁ * sFine - δ₀) * L)) := by
      gcongr
    _ = _ := by
      rw [← Real.rpow_sub hN, ← Real.rpow_add hN]
      congr 1
      ring

theorem native_time_ratio_le_strip_radius {N κ₁ sOld sFine δ₀ L ub : ℝ}
    {Told Tfine : ℕ} (hN : 1 ≤ N) (hL : 0 ≤ L)
    (hOld : (2 : ℝ) ^ Told ≤ N ^ ((κ₁ * sOld + δ₀) * L))
    (hFine : N ^ ((κ₁ * sFine - δ₀) * L) ≤ (2 : ℝ) ^ Tfine)
    (hgap : ub / 4 + 4 * δ₀ ≤ κ₁ * (sFine - sOld)) :
    N ^ (2 * δ₀ * L) * ((2 : ℝ) ^ Told / (2 : ℝ) ^ Tfine) ≤ N ^ (-(ub * L / 4)) := by
  apply (native_time_ratio_of_scale_bounds (zero_lt_one.trans_le hN) hOld hFine).trans
  apply Real.rpow_le_rpow_of_exponent_le hN
  have h := mul_le_mul_of_nonneg_right hgap hL
  nlinarith

end Submission.Lib.K4NativePreparationNumerics
