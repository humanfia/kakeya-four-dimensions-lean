-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/Thickness.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 3be7d21a,
-- Submission/Obl/k4_terminal_time_extension/Thickness.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.Interface
import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

/-- The exact dyadic thickness differs from its real power by at most two. -/
theorem delta_bounds {N : ℝ} (hN : 0 < N) (r : ℝ) :
    N ^ (-r) ≤ δ N r ∧ δ N r ≤ 2 * N ^ (-r) :=
  Submission.Obl.k4_profile_density_bounds.width_bounds hN r

/-- Lower comparison when the fitting depth decreases. -/
theorem delta_shift_lower {N : ℝ} (hN : 0 < N) (L s : ℝ) :
    δ N L * N ^ s / 2 ≤ δ N (L - s) := by
  calc
    δ N L * N ^ s / 2 ≤ (2 * N ^ (-L)) * N ^ s / 2 := by
      gcongr
      exact (delta_bounds hN L).2
    _ = N ^ (-(L - s)) := by
      rw [show (2 * N ^ (-L)) * N ^ s / 2 = N ^ (-L) * N ^ s by ring,
        ← Real.rpow_add hN]
      congr 1
      ring
    _ ≤ δ N (L - s) := (delta_bounds hN _).1

/-- Upper comparison when the fitting depth decreases. -/
theorem delta_shift_upper {N : ℝ} (hN : 0 < N) (L s : ℝ) :
    δ N (L - s) ≤ 2 * δ N L * N ^ s := by
  calc
    δ N (L - s) ≤ 2 * N ^ (-(L - s)) := (delta_bounds hN _).2
    _ = 2 * N ^ (-L) * N ^ s := by
      rw [mul_assoc, ← Real.rpow_add hN]
      congr 2
      ring
    _ ≤ 2 * δ N L * N ^ s := by
      gcongr
      exact (delta_bounds hN L).1

/-- One additional positive power absorbs both dyadic rounding factors. -/
theorem delta_absorb_power {N a : ℝ} (hN : 0 < N) (ha : 2 ≤ N ^ a)
    (L b : ℝ) : δ N L * N ^ b ≤ δ N (L - (b + a)) := by
  calc
    δ N L * N ^ b ≤ δ N L * N ^ b * N ^ a / 2 := by
      have hpos : 0 ≤ δ N L * N ^ b := by unfold δ; positivity
      nlinarith [mul_le_mul_of_nonneg_left ha hpos]
    _ = δ N L * N ^ (b + a) / 2 := by rw [mul_assoc, ← Real.rpow_add hN]
    _ ≤ _ := delta_shift_lower hN L (b + a)

/-- Nonnegative fitting depths have thickness at most one. -/
theorem delta_le_one {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) : δ N r ≤ 1 := by
  have hexp : 0 ≤ r * Real.log N / Real.log 2 :=
    div_nonneg (mul_nonneg hr (Real.log_nonneg hN)) (Real.log_pos (by norm_num)).le
  have hfloor : (0 : ℤ) ≤ ⌊r * Real.log N / Real.log 2⌋ := Int.floor_nonneg.mpr hexp
  exact zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
