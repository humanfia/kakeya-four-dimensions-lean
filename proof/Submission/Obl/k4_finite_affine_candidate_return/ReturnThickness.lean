-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/ReturnThickness.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.Original
import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_finite_affine_candidate_return

noncomputable section

/-- The true original thickness after a tangent gain is comparable to
parent thickness times native thickness. Both directions include the
actual old-depth rounding error and only the dyadic factor two. -/
theorem tangent_thickness_comparison
    {N : ℝ} (hN : 1 ≤ N) (parent child unit s v error : ℝ)
    (hdepth : |child - parent - unit * s| ≤ error) :
    δ N parent * (N ^ unit) ^ (-s - v) ≤
        (2 * N ^ error) * δ N (child + unit * v) ∧
      δ N (child + unit * v) ≤
        (2 * N ^ error) * (δ N parent * (N ^ unit) ^ (-s - v)) := by
  have hN0 : 0 < N := by linarith
  have hbounds (r : ℝ) : N ^ (-r) ≤ δ N r ∧ δ N r ≤ 2 * N ^ (-r) :=
    Submission.Obl.k4_profile_density_bounds.width_bounds hN0 r
  have hnative : (N ^ unit) ^ (-s - v) = N ^ (unit * (-s - v)) :=
    (Real.rpow_mul hN0.le unit (-s - v)).symm
  have hround := abs_le.mp hdepth
  rw [hnative]
  constructor
  · calc
      _ ≤ (2 * N ^ (-parent)) * N ^ (unit * (-s - v)) :=
        mul_le_mul_of_nonneg_right (hbounds parent).2 (by positivity)
      _ = 2 * N ^ (-parent + unit * (-s - v)) := by rw [Real.rpow_add hN0]; ring
      _ ≤ 2 * N ^ (error + -(child + unit * v)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by norm_num)
      _ = (2 * N ^ error) * N ^ (-(child + unit * v)) := by rw [Real.rpow_add hN0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbounds _).1 (by positivity)
  · calc
      _ ≤ 2 * N ^ (-(child + unit * v)) := (hbounds _).2
      _ ≤ 2 * N ^ (error + (-parent + unit * (-s - v))) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by norm_num)
      _ = (2 * N ^ error) * (N ^ (-parent) * N ^ (unit * (-s - v))) := by
        rw [Real.rpow_add hN0, Real.rpow_add hN0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hbounds parent).1 (by positivity)) (by positivity)

/-- Two-sided thickness comparison supplies both value and curvature
allowances with the same fit constant. -/
theorem return_fit_allowances
    {δ a a₀ H C J : ℝ} (hH : 0 ≤ H) (ha₀ : 0 ≤ a₀) (hδa : 0 ≤ δ * a)
    (hleft : δ * a ≤ J * a₀) (hright : a₀ ≤ J * (δ * a)) (hC : J * H ≤ C) :
    δ * (H * a) ≤ C * a₀ ∧ H * a₀ ≤ C * δ * a := by
  constructor
  · calc
      _ = H * (δ * a) := by ring
      _ ≤ H * (J * a₀) := mul_le_mul_of_nonneg_left hleft hH
      _ = (J * H) * a₀ := by ring
      _ ≤ C * a₀ := mul_le_mul_of_nonneg_right hC ha₀
  · calc
      _ ≤ H * (J * (δ * a)) := mul_le_mul_of_nonneg_left hright hH
      _ = (J * H) * (δ * a) := by ring
      _ ≤ C * (δ * a) := mul_le_mul_of_nonneg_right hC hδa
      _ = _ := by ring

end

end Submission.Obl.k4_finite_affine_candidate_return
