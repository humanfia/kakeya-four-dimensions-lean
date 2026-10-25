/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

import Submission.Obl.k4_dyadic_crop_affine_laws.Interface
import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_dyadic_crop_affine_laws

lemma scale_pos (N : ℕ → ℝ) (k : ℕ) (r : ℝ) : 0 < Scale N k r := by
  simpa only [Scale, k4_profile_density_bounds.width] using
    k4_profile_density_bounds.width_pos (N k) r

lemma scale_le_two_rpow (N : ℕ → ℝ) (k : ℕ) (r : ℝ) (hN : 0 < N k) :
    Scale N k r ≤ 2 * N k ^ (-r) := by
  simpa only [Scale, k4_profile_density_bounds.width] using
    (k4_profile_density_bounds.width_bounds hN r).2

lemma rpow_le_scale (N : ℕ → ℝ) (k : ℕ) (r : ℝ) (hN : 0 < N k) :
    N k ^ (-r) ≤ Scale N k r := by
  simpa only [Scale, k4_profile_density_bounds.width] using
    (k4_profile_density_bounds.width_bounds hN r).1

lemma scale_sq_le_four_rpow (N : ℕ → ℝ) (k : ℕ) (r : ℝ) (hN : 0 < N k) :
    Scale N k r ^ 2 ≤ 4 * N k ^ (-2 * r) := by
  have hscale := scale_le_two_rpow N k r hN
  have hscale0 := scale_pos N k r
  have hq : (N k ^ (-r)) ^ 2 = N k ^ (-2 * r) := by
    calc
      (N k ^ (-r)) ^ 2 = (N k ^ (-r)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = N k ^ ((-r) * 2) := (Real.rpow_mul hN.le (-r) 2).symm
      _ = N k ^ (-2 * r) := by congr 1; ring
  calc
    Scale N k r ^ 2 ≤ (2 * N k ^ (-r)) ^ 2 := by nlinarith
    _ = 4 * (N k ^ (-r)) ^ 2 := by ring
    _ = 4 * N k ^ (-2 * r) := by rw [hq]

end Submission.Obl.k4_dyadic_crop_affine_laws
