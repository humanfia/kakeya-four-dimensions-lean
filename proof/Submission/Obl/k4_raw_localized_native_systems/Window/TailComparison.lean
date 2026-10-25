import Submission.Obl.k4_raw_localized_native_systems.Window.DensityGood
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- Fixed multiples of two power tails eventually lie strictly below the
original inverse-subpower source coverage. -/
theorem eventually_source_tail_lt {N κ : ℕ → ℝ} {X₁ X₂ : ℕ → ENNReal}
    (hN : ∀ n, 1 ≤ N n) (hNt : Tendsto N atTop atTop) (hκ : ∀ n, 1 ≤ κ n)
    (hsub : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, κ n ≤ N n ^ e)
    (hX₁ : IsPowerSmall N X₁) (hX₂ : IsPowerSmall N X₂) :
    ∀ᶠ n in atTop, 10 * X₁ n + 2 * X₂ n < ENNReal.ofReal ((κ n)⁻¹) := by
  obtain ⟨c₁, hc₁, hx₁⟩ := hX₁
  obtain ⟨c₂, hc₂, hx₂⟩ := hX₂
  let c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  have hbudget := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hκ hsub 1 (show -c < 0 by linarith) (by norm_num : (0 : ℝ) ≤ 12)
  filter_upwards [hx₁, hx₂, hbudget] with n hn₁ hn₂ hnB
  have hN0 : 0 < N n := lt_of_lt_of_le zero_lt_one (hN n)
  have hκ0 : 0 < κ n := lt_of_lt_of_le zero_lt_one (hκ n)
  have hpow : 0 ≤ N n ^ (-c) := Real.rpow_nonneg hN0.le _
  have h₁ : X₁ n ≤ ENNReal.ofReal (N n ^ (-c)) := hn₁.trans
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN n)
      (neg_le_neg (min_le_left _ _))))
  have h₂ : X₂ n ≤ ENNReal.ofReal (N n ^ (-c)) := hn₂.trans
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN n)
      (neg_le_neg (min_le_right _ _))))
  have hreal : 12 * N n ^ (-c) < (κ n)⁻¹ := by
    rw [← one_div, lt_div_iff₀ hκ0]
    simpa only [pow_one, Real.rpow_zero, mul_comm, mul_left_comm, mul_assoc] using hnB
  calc
    _ ≤ 10 * ENNReal.ofReal (N n ^ (-c)) + 2 * ENNReal.ofReal (N n ^ (-c)) := by gcongr
    _ = ENNReal.ofReal (12 * N n ^ (-c)) := by
      rw [show (10 : ENNReal) = ENNReal.ofReal 10 by norm_num,
        show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal

end Submission.Obl.k4_raw_localized_native_systems.Window
