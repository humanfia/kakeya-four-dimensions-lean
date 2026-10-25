import Submission.Obl.k4_raw_localized_native_systems.Window.SlackBounds
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open Filter
open Submission.Obl.k4_finite_width_output_exclusion

/-- The raw scalar, density and loose inverse-cutoff budgets hold eventually
on the same sequence whenever the actual earlier slack is subpower. -/
theorem eventually_raw_bounds {N κ : ℕ → ℝ}
    (hN : ∀ j, 1 ≤ N j) (hNt : Tendsto N atTop atTop)
    (hκ : ∀ j, 1 ≤ κ j)
    (hsub : ∀ a : ℝ, 0 < a → ∀ᶠ j in atTop, κ j ≤ N j ^ a)
    {χ τ u ε r s : ℝ} (hχ : 0 < χ) (hτχ : τ < χ) (hu : u < 1)
    (hε : 0 < ε) (hgap : r + ε ≤ s) (hclose : s - r + 2 * ε ≤ 2 * χ) :
    ∀ᶠ j in atTop,
      256 ≤ N j ∧ 2 ≤ N j ^ χ ∧
      64 * κ j ^ 3 * N j ^ τ ≤ N j ^ χ ∧
      1 + κ j ≤ N j ^ χ ∧ κ j ≤ N j ∧
      32 * κ j * N j ^ u ≤ N j ∧
      κ j * δ (N j) r ≤ N j ^ χ * N j ^ (-s + χ) ∧
      κ j / δ (N j) r ≤ N j ^ χ / N j ^ (-s + χ) := by
  have hdensity := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hκ hsub 3 hτχ (by norm_num : (0 : ℝ) ≤ 64)
  have hscale := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hκ hsub 1 (show (0 : ℝ) < χ from hχ) (by norm_num : (0 : ℝ) ≤ 2)
  have hangle := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hκ hsub 1 hu (by norm_num : (0 : ℝ) ≤ 32)
  have htwoε := k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show (0 : ℝ) < ε from hε) 2
  have htwoχ := k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show (0 : ℝ) < χ from hχ) 2
  filter_upwards [hNt.eventually_ge_atTop 256, hdensity, hscale, hangle,
    htwoε, htwoχ, hsub ε hε, hsub 1 zero_lt_one] with j hjN hjD hjS hjA hjε hjχ hjκ hjκ1
  have htwo : 2 ≤ N j ^ ε := by simpa only [Real.rpow_zero, mul_one] using hjε.le
  have hpow : 2 ≤ N j ^ χ := by simpa only [Real.rpow_zero, mul_one] using hjχ.le
  have hS : 2 * κ j ≤ N j ^ χ := by
    simpa only [pow_one, Real.rpow_zero, mul_one] using hjS.le
  have hA : 32 * κ j * N j ^ u ≤ N j := by
    simpa only [pow_one, Real.rpow_one] using hjA.le
  obtain ⟨hvalue, hcurv⟩ := raw_test_slack_bounds (hN j)
    (by linarith [hκ j] : 0 ≤ κ j) hjκ hgap hclose htwo
  exact ⟨hjN, hpow, hjD.le, (show 1 + κ j ≤ 2 * κ j by linarith only [hκ j]).trans hS,
    by simpa using hjκ1,
    hA, hvalue, hcurv⟩

end Submission.Obl.k4_raw_localized_native_systems.Window
