-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/ScaleTransfer.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.Interface
import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

/-- The dyadic scale remains between the unrounded power and twice that power. -/
theorem δ_bounds {N : ℝ} (hN : 0 < N) (r : ℝ) :
    N ^ (-r) ≤ δ N r ∧ δ N r ≤ 2 * N ^ (-r) :=
  Submission.Obl.k4_profile_density_bounds.width_bounds hN r

/-- Transferring a quadratic upper bound between two depths loses only the
power of their difference and one dyadic rounding factor. -/
theorem δ_transfer {N : ℝ} (hN : 0 < N) (r s : ℝ) :
    δ N r ≤ 2 * N ^ (s - r) * δ N s := by
  have hprod : N ^ (s - r) * N ^ (-s) = N ^ (-r) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    δ N r ≤ 2 * N ^ (-r) := (δ_bounds hN r).2
    _ = (2 * N ^ (s - r)) * N ^ (-s) := by rw [mul_assoc, hprod]
    _ ≤ (2 * N ^ (s - r)) * δ N s :=
      mul_le_mul_of_nonneg_left (δ_bounds hN s).1 (by positivity)

/-- Down-rounding an actual candidate gain preserves its fit up to the exact
power allowed by the gain-menu spacing. -/
theorem rounded_gain_scales {N : ℝ} (hN : 1 ≤ N) (r L h h' step : ℝ)
    (hL : 0 ≤ L) (hle : h' ≤ h) (hgap : h ≤ h' + step) :
    δ N (r + h * L) ≤ 2 * δ N (r + h' * L) ∧
      δ N (r + h' * L) ≤ 2 * N ^ (step * L) * δ N (r + h * L) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ ((r + h' * L) - (r + h * L)) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hN
      (show (r + h' * L) - (r + h * L) ≤ 0 from by
        nlinarith [mul_le_mul_of_nonneg_right hle hL])
  have hpow' : N ^ ((r + h * L) - (r + h' * L)) ≤ N ^ (step * L) :=
    Real.rpow_le_rpow_of_exponent_le hN (by
      nlinarith [mul_le_mul_of_nonneg_right hgap hL])
  constructor
  · calc
      _ ≤ 2 * N ^ ((r + h' * L) - (r + h * L)) * δ N (r + h' * L) := δ_transfer hNpos _ _
      _ ≤ 2 * δ N (r + h' * L) := by
        have hδ : 0 ≤ δ N (r + h' * L) := (δ_bounds hNpos _).1.trans' (by positivity)
        nlinarith [mul_le_mul_of_nonneg_right hpow hδ]
  · exact (δ_transfer hNpos _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow' (by positivity))
        ((δ_bounds hNpos _).1.trans' (by positivity)))

end Submission.Obl.k4_quadratic_finite_greedy_cover
