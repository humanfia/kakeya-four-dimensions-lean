/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/NormalizedPredictors.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_intercept_concentration.Inherited.AffineResidualTransport

namespace Submission.Obl.k4_critical_intercept_concentration

open Inherited

noncomputable section

/-- Affine coefficients in the actual contact coordinates of a parent. -/
def normalizedPredictor (H t₀ z₀ y₀ v₀ : ℝ) (A : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![A 0 + t₀ * A 1 + z₀ * A 2 + y₀ * A 3,
    H * (A 1 + v₀ * A 2 + (-z₀ + t₀ * v₀) * A 3),
    H * (A 2 + t₀ * A 3), H ^ 2 * A 3]

theorem normalizedPredictor_unframe (H t₀ z₀ y₀ v₀ : ℝ) (A : Fin 4 → ℝ)
    (q : Fin 3 → ℝ) :
    affineBaseEval A (horizontalUnframe H t₀ z₀ y₀ v₀ q) =
      affineBaseEval (normalizedPredictor H t₀ z₀ y₀ v₀ A) q := by
  dsimp [affineBaseEval, horizontalUnframe, normalizedPredictor]
  ring

theorem normalizedPredictor_frame (H t₀ z₀ y₀ v₀ : ℝ) (hH : H ≠ 0)
    (A : Fin 4 → ℝ) (q : Fin 3 → ℝ) :
    affineBaseEval (normalizedPredictor H t₀ z₀ y₀ v₀ A)
        (horizontalFrame H t₀ z₀ y₀ v₀ q) = affineBaseEval A q := by
  rw [← normalizedPredictor_unframe, horizontalUnframe_frame _ _ _ _ _ hH]

/-- A physical slope of size M becomes O(K*H*M) after contact normalization.
In particular a primitive slope of size subpower/H becomes subpower again. -/
theorem normalizedPredictor_slope_bound (H t₀ z₀ y₀ v₀ K M : ℝ) (A : Fin 4 → ℝ)
    (hH : 0 ≤ H) (hH1 : H ≤ 1) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (ht₀ : |t₀| ≤ 1) (hz₀ : |z₀| ≤ K) (hv₀ : |v₀| ≤ K)
    (hA : ∀ i : Fin 3, |A i.succ| ≤ M) :
    ∀ i : Fin 3, |normalizedPredictor H t₀ z₀ y₀ v₀ A i.succ| ≤ 4 * K * H * M := by
  have hK0 : 0 ≤ K := by linarith
  have hA1 : |A 1| ≤ M := hA 0
  have hA2 : |A 2| ≤ M := hA 1
  have hA3 : |A 3| ≤ M := hA 2
  have htv : |t₀ * v₀| ≤ K := by
    rw [abs_mul]
    exact (mul_le_mul ht₀ hv₀ (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hcoeff : |-z₀ + t₀ * v₀| ≤ 2 * K :=
    (abs_add_le _ _).trans (by simpa [two_mul] using add_le_add hz₀ htv)
  have hm : M ≤ K * M := by nlinarith only [mul_le_mul_of_nonneg_right hK hM]
  intro i
  fin_cases i
  · change |H * (A 1 + v₀ * A 2 + (-z₀ + t₀ * v₀) * A 3)| ≤ _
    rw [abs_mul, abs_of_nonneg hH]
    have hsum : |A 1 + v₀ * A 2 + (-z₀ + t₀ * v₀) * A 3| ≤ M + K * M + (2 * K) * M := by
      apply (abs_add_le _ _).trans
      apply add_le_add
      · apply (abs_add_le _ _).trans
        apply add_le_add hA1
        rw [abs_mul]
        exact mul_le_mul hv₀ hA2 (abs_nonneg _) hK0
      · rw [abs_mul]
        exact mul_le_mul hcoeff hA3 (abs_nonneg _) (by positivity)
    exact (mul_le_mul_of_nonneg_left hsum hH).trans (by nlinarith [mul_le_mul_of_nonneg_left hm hH])
  · change |H * (A 2 + t₀ * A 3)| ≤ _
    rw [abs_mul, abs_of_nonneg hH]
    have hsum : |A 2 + t₀ * A 3| ≤ 2 * M := by
      apply (abs_add_le _ _).trans
      have hh : |t₀ * A 3| ≤ M := by
        rw [abs_mul]
        exact (mul_le_mul ht₀ hA3 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      linarith
    exact (mul_le_mul_of_nonneg_left hsum hH).trans (by nlinarith [mul_le_mul_of_nonneg_left hm hH])
  · change |H ^ 2 * A 3| ≤ _
    rw [abs_mul, abs_of_nonneg (sq_nonneg H)]
    have hsq : H ^ 2 ≤ H := by nlinarith
    have hh := mul_le_mul hsq hA3 (abs_nonneg _) hH
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hm hH, mul_nonneg hH hM])

/-- Exact midpoint intercept prediction on the normalized base cells. -/
theorem midpoint_intercept_prediction_normalized
    (L A : Fin 4 → ℝ) (b : Fin 6 → ℝ)
    (H t₀ z₀ y₀ v₀ tm t a K E : ℝ) (hH : 0 < H)
    (hfit : |affineResidualIntercept L b + t * affineResidualSlope L b| ≤ K * a)
    (hslope : |affineResidualSlope A b| ≤ E) (ht : |tm - t| ≤ H)
    (hsmall : H * E ≤ K * a) :
    |(affineResidualIntercept A b + tm * affineResidualSlope A b) -
      affineBaseEval (normalizedPredictor H t₀ z₀ y₀ v₀ (L - A))
        (horizontalFrame H t₀ z₀ y₀ v₀ (nativeHorizontalLine b t))| ≤ 2 * K * a := by
  rw [normalizedPredictor_frame _ _ _ _ _ hH.ne']
  exact affineResidual_midpoint_prediction A L b tm t a K H E hH.le hfit hslope ht hsmall

end

end Submission.Obl.k4_critical_intercept_concentration
