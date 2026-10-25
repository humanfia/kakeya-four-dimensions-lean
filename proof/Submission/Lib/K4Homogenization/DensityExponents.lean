/-
Adapted from: here:o018
-/
import Mathlib

/-! Logarithmic exponents of selected densities. The factor-two dyadic ambiguity
and a small restriction loss become vanishing errors in the exponent tables. -/

open Filter
open scoped Topology

namespace Submission.Lib.K4Homogenization

noncomputable def densityExponent (N a : ℝ) : ℝ := -Real.log a / Real.log N

theorem selected_density_exponent_bound {N C a : ℝ} (hN : 2 ≤ N)
    (ha₀ : N ^ (-C) / 2 ≤ a) (ha₁ : a ≤ N ^ C / 2) :
    |densityExponent N a| ≤ C + 1 := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hlo : N ^ (-C - 1) ≤ a := by
    calc
      N ^ (-C - 1) = N ^ (-C) / N := by rw [Real.rpow_sub hN0, Real.rpow_one]
      _ ≤ N ^ (-C) / 2 := div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) (by norm_num) hN
      _ ≤ a := ha₀
  have hhi : a ≤ N ^ (C + 1) := by
    apply ha₁.trans
    calc
      N ^ C / 2 ≤ N ^ C := by linarith [Real.rpow_pos_of_pos hN0 C]
      _ ≤ N ^ (C + 1) := Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
  have ha : 0 < a := (Real.rpow_pos_of_pos hN0 _).trans_le hlo
  have hloglo := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hlo
  have hloghi := Real.log_le_log ha hhi
  rw [Real.log_rpow hN0] at hloglo hloghi
  apply abs_le.mpr
  constructor
  · rw [densityExponent, le_div_iff₀ hlogN]
    nlinarith
  · rw [densityExponent, div_le_iff₀ hlogN]
    nlinarith

/-- A small multiplicative restriction loss changes the logarithmic density exponent by
at most that loss exponent and the dyadic rounding error. -/
theorem restricted_density_exponent_error {N a b τ : ℝ} (hN : 1 < N) (ha : 0 < a)
    (hτ : 0 ≤ τ) (hb₀ : N ^ (-τ) * a ≤ b) (hb₁ : b ≤ 2 * a) :
    |densityExponent N b - densityExponent N a| ≤ τ + Real.log 2 / Real.log N := by
  have hN0 : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hpow : 0 < N ^ (-τ) := Real.rpow_pos_of_pos hN0 _
  have hb : 0 < b := (mul_pos hpow ha).trans_le hb₀
  have hloglo := Real.log_le_log (mul_pos hpow ha) hb₀
  have hloghi := Real.log_le_log hb hb₁
  rw [Real.log_mul hpow.ne' ha.ne', Real.log_rpow hN0] at hloglo
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha.ne'] at hloghi
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hprod : 0 ≤ τ * Real.log N := mul_nonneg hτ hlogN.le
  have habs : |Real.log b - Real.log a| ≤ τ * Real.log N + Real.log 2 :=
    abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have heq : densityExponent N b - densityExponent N a =
      -(Real.log b - Real.log a) / Real.log N := by unfold densityExponent; ring
  rw [heq, abs_div, abs_neg, abs_of_pos hlogN]
  calc
    |Real.log b - Real.log a| / Real.log N ≤
        (τ * Real.log N + Real.log 2) / Real.log N :=
      div_le_div_of_nonneg_right habs hlogN.le
    _ = τ + Real.log 2 / Real.log N := by field_simp [hlogN.ne']

theorem dyadic_density_rounding_tendsto_zero {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => Real.log 2 / Real.log (N n)) atTop (𝓝 0) :=
  (Real.tendsto_log_atTop.comp hN).const_div_atTop _

/-- The two explicit density ambiguities disappear simultaneously along a slowly chosen
sequence of restriction tolerances. -/
theorem density_exponent_error_tendsto_zero {N τ a b : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) (hτ : Tendsto τ atTop (𝓝 0))
    (hτ₀ : ∀ᶠ n in atTop, 0 ≤ τ n) (ha : ∀ᶠ n in atTop, 0 < a n)
    (hb₀ : ∀ᶠ n in atTop, N n ^ (-τ n) * a n ≤ b n)
    (hb₁ : ∀ᶠ n in atTop, b n ≤ 2 * a n) :
    Tendsto (fun n => |densityExponent (N n) (b n) - densityExponent (N n) (a n)|)
      atTop (𝓝 0) := by
  have hN1 : ∀ᶠ n in atTop, 1 < N n := hN.eventually (eventually_gt_atTop 1)
  have hbound : ∀ᶠ n in atTop,
      |densityExponent (N n) (b n) - densityExponent (N n) (a n)| ≤
        τ n + Real.log 2 / Real.log (N n) := by
    filter_upwards [hN1, hτ₀, ha, hb₀, hb₁] with n hn ht ha hb₀ hb₁
    exact restricted_density_exponent_error hn ha ht hb₀ hb₁
  have herr : Tendsto (fun n => τ n + Real.log 2 / Real.log (N n)) atTop (𝓝 0) := by
    simpa only [add_zero] using hτ.add (dyadic_density_rounding_tendsto_zero hN)
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound herr

end Submission.Lib.K4Homogenization
