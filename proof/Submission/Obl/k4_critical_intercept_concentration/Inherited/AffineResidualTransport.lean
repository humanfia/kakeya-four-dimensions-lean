/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/AffineResidualTransport.lean.
   Original source attributions below are preserved. -/
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/AffineResidualTransport.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_critical_intercept_concentration.Inherited.AffinePrimitive
import Submission.Obl.k4_critical_intercept_concentration.Inherited.AffineContactFit
import Submission.Obl.k4_critical_intercept_concentration.Inherited.HorizontalNormalization

/-! A midpoint intercept is predicted by each old affine entry on a fine cell. -/

namespace Submission.Obl.k4_critical_intercept_concentration.Inherited

noncomputable section

theorem affineResidualSlope_difference (A L : Fin 4 → ℝ) (b : Fin 6 → ℝ) :
    affineResidualSlope A b - affineResidualSlope L b =
      (L 1 - A 1) + (L 2 - A 2) * b 3 + (L 3 - A 3) * b 4 := by
  unfold affineResidualSlope
  ring

theorem affineResidual_midpoint_transport (A L : Fin 4 → ℝ) (b : Fin 6 → ℝ) (t₀ t : ℝ) :
    (affineResidualIntercept A b + t₀ * affineResidualSlope A b) -
      affineBaseEval (L - A) (nativeHorizontalLine b t) =
      (affineResidualIntercept L b + t * affineResidualSlope L b) +
        (t₀ - t) * affineResidualSlope A b := by
  dsimp [affineResidualIntercept, affineResidualSlope, affineBaseEval, nativeHorizontalLine]
  ring

theorem affineResidual_midpoint_prediction (A L : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    (t₀ t a K H E : ℝ) (hH : 0 ≤ H)
    (hfit : |affineResidualIntercept L b + t * affineResidualSlope L b| ≤ K * a)
    (hslope : |affineResidualSlope A b| ≤ E) (ht : |t₀ - t| ≤ H)
    (hsmall : H * E ≤ K * a) :
    |(affineResidualIntercept A b + t₀ * affineResidualSlope A b) -
      affineBaseEval (L - A) (nativeHorizontalLine b t)| ≤ 2 * K * a := by
  rw [affineResidual_midpoint_transport]
  calc
    _ ≤ |affineResidualIntercept L b + t * affineResidualSlope L b| +
        |(t₀ - t) * affineResidualSlope A b| := abs_add_le _ _
    _ ≤ K * a + H * E := by
      apply add_le_add hfit
      rw [abs_mul]
      exact mul_le_mul ht hslope (abs_nonneg _) hH
    _ ≤ _ := by linarith only [hsmall]

/-- A whole-block affine fit bounds its constant trajectory derivative. -/
theorem affineResidualSlope_le_of_block_fit (A : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    (t H E : ℝ) (hH : 0 < H)
    (hleft : |affineResidualIntercept A b + t * affineResidualSlope A b| ≤ E)
    (hright : |affineResidualIntercept A b + (t + H) * affineResidualSlope A b| ≤ E) :
    |affineResidualSlope A b| ≤ 2 * E / H := by
  apply (le_div_iff₀ hH).mpr
  calc
    _ = |H * affineResidualSlope A b| := by rw [abs_mul, abs_of_pos hH]; ring
    _ = |(affineResidualIntercept A b + (t + H) * affineResidualSlope A b) -
        (affineResidualIntercept A b + t * affineResidualSlope A b)| := by
      congr 1
      ring
    _ ≤ |affineResidualIntercept A b + (t + H) * affineResidualSlope A b| +
        |affineResidualIntercept A b + t * affineResidualSlope A b| := abs_sub _ _
    _ ≤ _ := by linarith only [hleft, hright]

end

end Submission.Obl.k4_critical_intercept_concentration.Inherited
