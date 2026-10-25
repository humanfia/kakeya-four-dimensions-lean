/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativePredictor.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.PredictorMatching
import Submission.Obl.k4_horizontal_strict_parameter_step.ReconstructionMesh
import Submission.Lib.K4FullTimeLayers.Geometry

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set
open Submission.Lib.K4FullTimeLayers

/-- Pull a physical true affine fit back along the common reference velocity.
It has exactly the six-coefficient form of an old full-time predictor. -/
abbrev affinePredictor := liftAffine

/-- The pullback error is paid only by the velocity-bin width and the original
contact defect. No coefficient intercept enters this estimate. -/
theorem affinePredictor_fit (L : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    {v t χ K a M : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hvel : |b 3 - v| ≤ χ) (hdef : |b 4 + b 0| ≤ χ)
    (hL2 : |L 2| ≤ M) (hL3 : |L 3| ≤ M)
    (hfit : |b 2 + t * b 5 -
      (L 0 + L 1 * t + L 2 * (b 0 + t * b 3) + L 3 * (b 1 + t * b 4))| ≤ K * a) :
    |b 2 + t * b 5 - predictor (affinePredictor L v) t (b 0) (b 1)| ≤
      K * a + 2 * M * χ := by
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hvel
  have hh := affine_fit_to_parameter ht hdef hvel hfit
  change |b 2 + t * b 5 - parameterPredictor (liftAffine L v) t (b 0) (b 1)| ≤ _
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hL2 hχ,
    mul_le_mul_of_nonneg_right hL3 hχ])

/-- True affine slopes control the pulled-back spatial gradients at all padded
jitter times. The bound is independent of any absolute affine intercept. -/
theorem affinePredictor_gradients (L : Fin 4 → ℝ) (v : ℝ) {t M : ℝ}
    (ht : |t| ≤ 2) (hL2 : |L 2| ≤ M) (hL3 : |L 3| ≤ M) :
    |affinePredictor L v 2 + affinePredictor L v 3 * t| ≤ 3 * M ∧
      |affinePredictor L v 4 + affinePredictor L v 5 * t| ≤ M := by
  constructor
  · change |L 2 + -L 3 * t| ≤ 3 * M
    calc
      _ ≤ |L 2| + |-L 3 * t| := abs_add_le _ _
      _ ≤ M + M * 2 := by
        rw [abs_mul, abs_neg]
        exact add_le_add hL2 (mul_le_mul hL3 ht (abs_nonneg _) ((abs_nonneg _).trans hL2))
      _ = _ := by ring
  · simpa only [affinePredictor, liftAffine, Matrix.cons_val, Matrix.head_cons, zero_mul, add_zero]
      using hL3

theorem affinePredictor_time_slope (L : Fin 4 → ℝ) {v p q M K : ℝ}
    (hL1 : |L 1| ≤ M) (hL2 : |L 2| ≤ M) (hL3 : |L 3| ≤ M)
    (hv : |v| ≤ K) (hp : |p| ≤ K) :
    |predictorTimeSlope (affinePredictor L v) p q| ≤ M * (1 + 2 * K) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hL1
  have hK : 0 ≤ K := (abs_nonneg _).trans hv
  change |L 1 + v * L 2 + -L 3 * p + 0 * q| ≤ _
  rw [zero_mul, add_zero]
  calc
    _ ≤ |L 1| + |v * L 2| + |-L 3 * p| := abs_add_three _ _ _
    _ ≤ M + M * K + M * K := by
      rw [abs_mul, abs_mul, abs_neg]
      exact add_le_add (add_le_add hL1 (by
        simpa only [mul_comm] using mul_le_mul hv hL2 (abs_nonneg _) hK))
        (mul_le_mul hL3 hp (abs_nonneg _) hM)
    _ = _ := by ring

end Submission.Obl.k4_horizontal_strict_parameter_step
