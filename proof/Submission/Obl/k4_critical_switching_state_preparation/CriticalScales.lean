/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/CriticalScales.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/CriticalScales.lean.
   Original source attributions below are preserved. -/
import Mathlib

namespace Submission.Obl.k4_critical_switching_state_preparation

/-- The actual dyadic time length is comparable with the horizontal scale,
with exactly the same slack as the frozen time-rate bounds. -/
theorem time_length_comparison {N K κ s : ℝ} {T : ℕ}
    (hN : 0 < N) (hK : 0 < K)
    (hlo : N ^ (κ * s) / K ≤ (2 : ℝ) ^ T)
    (hhi : (2 : ℝ) ^ T ≤ K * N ^ (κ * s)) :
    ((2 : ℝ) ^ T)⁻¹ / K ≤ N ^ (-κ * s) ∧
      N ^ (-κ * s) ≤ K * ((2 : ℝ) ^ T)⁻¹ := by
  have hpow : 0 < N ^ (κ * s) := Real.rpow_pos_of_pos hN _
  have htwo : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have hneg : N ^ (-κ * s) = (N ^ (κ * s))⁻¹ := by
    rw [show -κ * s = -(κ * s) by ring, Real.rpow_neg hN.le]
  rw [hneg]
  constructor
  · calc
      ((2 : ℝ) ^ T)⁻¹ / K = (K * (2 : ℝ) ^ T)⁻¹ := by
        simp [mul_inv_rev, div_eq_mul_inv]
      _ ≤ (N ^ (κ * s))⁻¹ :=
        inv_anti₀ hpow (by simpa only [mul_comm] using (div_le_iff₀ hK).mp hlo)
  · apply (le_div_iff₀ htwo).mpr
    have hdiv : (2 : ℝ) ^ T / N ^ (κ * s) ≤ K :=
      (div_le_iff₀ hpow).mpr (by simpa only [mul_comm] using hhi)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- Convert the frozen `q²*g` prior bounds into critical spatial `q³`
bounds. This costs only two powers of the original slack. -/
theorem assignment_bounds_from_time_comparison {N K κ s d m : ℝ} {T : ℕ}
    (hN : 0 < N) (hK : 0 < K)
    (hlo : N ^ (κ * s) / K ≤ (2 : ℝ) ^ T)
    (hhi : (2 : ℝ) ^ T ≤ K * N ^ (κ * s))
    (hmlo : (N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ 2 * N ^ (-κ * s) / K ≤ m)
    (hmhi : m ≤ K * (N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ 2 * N ^ (-κ * s)) :
    ((2 : ℝ) ^ T)⁻¹ ^ 3 * (N ^ (-s)) ^ d / K ^ 2 ≤ m ∧
      m ≤ K ^ 2 * ((2 : ℝ) ^ T)⁻¹ ^ 3 * (N ^ (-s)) ^ d := by
  have hcmp := time_length_comparison hN hK hlo hhi
  have had : 0 < (N ^ (-s)) ^ d :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN _) _
  constructor
  · calc
      _ = (N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ 2 *
          (((2 : ℝ) ^ T)⁻¹ / K) / K := by field_simp
      _ ≤ (N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ 2 * N ^ (-κ * s) / K := by gcongr; exact hcmp.1
      _ ≤ m := hmlo
  · calc
      m ≤ K * (N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ 2 * N ^ (-κ * s) := hmhi
      _ ≤ K * (N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ 2 *
          (K * ((2 : ℝ) ^ T)⁻¹) := by gcongr; exact hcmp.2
      _ = _ := by ring


/-- At the critical rate, the hidden width is the square of the horizontal
power scale; both ratios in the affine slope assumptions are subpower. -/
theorem critical_hidden_time_ratios {N K κ s : ℝ} {T : ℕ}
    (hN1 : 1 ≤ N) (hN : 0 < N) (hK : 0 < K) (hκ : 0 ≤ κ) (hs : 0 ≤ s)
    (hcritical : 2 * κ = 1)
    (hlo : N ^ (κ * s) / K ≤ (2 : ℝ) ^ T)
    (hhi : (2 : ℝ) ^ T ≤ K * N ^ (κ * s)) :
    N ^ (-s) / ((2 : ℝ) ^ T)⁻¹ ≤ K ∧
      N ^ (-s) / (((2 : ℝ) ^ T)⁻¹ ^ 2) ≤ K ^ 2 := by
  have hg := (time_length_comparison hN hK hlo hhi).2
  have hg0 : 0 < N ^ (-κ * s) := Real.rpow_pos_of_pos hN _
  have hg1 : N ^ (-κ * s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith only [mul_nonneg hκ hs])
  have hq : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hsquare : N ^ (-s) = (N ^ (-κ * s)) ^ 2 := by
    have he : -s = -κ * s + -κ * s := by
      nlinarith only [congrArg (fun r : ℝ => r * s) hcritical]
    rw [he, Real.rpow_add hN, pow_two]
  rw [hsquare]
  constructor
  · apply (div_le_iff₀ hq).mpr
    have hh : (N ^ (-κ * s)) ^ 2 ≤ N ^ (-κ * s) := by nlinarith
    exact hh.trans hg
  · apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
    have hh := pow_le_pow_left₀ hg0.le hg 2
    nlinarith only [hh]

end Submission.Obl.k4_critical_switching_state_preparation
