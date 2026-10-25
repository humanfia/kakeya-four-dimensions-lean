/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.AffineCrop
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.Conditioning

namespace Submission.Obl.k4_dyadic_crop_affine_laws.Framework

open MeasureTheory Set
open scoped ENNReal

/-- The native slope ceiling under a planar crop is multiplied by `a²` and
by the reciprocal prior mass of its crop cell. -/
theorem conditioned_crop_slope_bound
    (ν : Measure Coefficients) (A : Set Coefficients)
    (a : ℝ) (ha : 0 < a) (c v : Fin 2 → ℝ) (Λ : ℝ)
    (hΛ : ∀ Z : Set (EuclideanSpace ℝ (Fin 3)),
      ν {l | slopeVector l ∈ Z} ≤ ENNReal.ofReal Λ * volume Z)
    (Z : Set (EuclideanSpace ℝ (Fin 3))) :
    conditionedPrior ν A (cropTrajectoryEquiv a ha.ne' c v).symm
        {l | slopeVector l ∈ Z} ≤
      ((ν A)⁻¹ * ENNReal.ofReal Λ * ENNReal.ofReal (a ^ 2)) * volume Z := by
  have hcomm (l : Coefficients) :
      slopeVector ((cropTrajectoryEquiv a ha.ne' c v).symm l) =
        (cropSlopeEquiv a ha.ne' v).symm (slopeVector l) := by
    apply (cropSlopeEquiv a ha.ne' v).injective
    rw [MeasurableEquiv.apply_symm_apply, ← crop_slopeVector,
      MeasurableEquiv.apply_symm_apply]
  exact conditionedPrior_marginal_bound ν A (cropTrajectoryEquiv a ha.ne' c v).symm
    slopeVector slopeVector (cropSlopeEquiv a ha.ne' v).symm hcomm volume volume
    (ENNReal.ofReal Λ) (ENNReal.ofReal (a ^ 2)) hΛ
    (map_cropSlopeEquiv_symm a ha v) Z

/-- Real-valued version of the exact cropped slope ceiling. -/
theorem conditioned_crop_slope_bound_real
    (ν : Measure Coefficients) (A : Set Coefficients)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ∞)
    (a : ℝ) (ha : 0 < a) (c v : Fin 2 → ℝ) (Λ : ℝ)
    (hΛ : ∀ Z : Set (EuclideanSpace ℝ (Fin 3)),
      ν {l | slopeVector l ∈ Z} ≤ ENNReal.ofReal Λ * volume Z)
    (Z : Set (EuclideanSpace ℝ (Fin 3))) :
    conditionedPrior ν A (cropTrajectoryEquiv a ha.ne' c v).symm
        {l | slopeVector l ∈ Z} ≤
      ENNReal.ofReal (a ^ 2 * Λ / (ν A).toReal) * volume Z := by
  have hm : ENNReal.ofReal (a ^ 2 * Λ / (ν A).toReal) =
      (ν A)⁻¹ * ENNReal.ofReal Λ * ENNReal.ofReal (a ^ 2) := by
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hA hAfin),
      ENNReal.ofReal_toReal hAfin, ENNReal.ofReal_mul (sq_nonneg a), div_eq_mul_inv]
    ac_rfl
  rw [hm]
  exact conditioned_crop_slope_bound ν A a ha c v Λ hΛ Z

end Submission.Obl.k4_dyadic_crop_affine_laws.Framework
