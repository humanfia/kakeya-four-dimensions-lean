/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at c7228243ba9237e7d6cd8a43298ef6dbf77acd93, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/ResidualSupport.lean`.
Only the namespace and internal imports are changed; unused NativeComparison import removed. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NormalizedResidual
import Submission.Lib.K4FullTimeLayers.Geometry

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set
open Submission.Lib.K4FullTimeLayers

/-- Ordinary affine slope agreement controls both spatial derivatives after
pullback along the SAME reference velocity. -/
theorem liftAffine_difference_gradients (L P : Fin 4 → ℝ) (v : ℝ) {t M : ℝ}
    (ht : |t| ≤ 2) (hL₂ : |L 2 - P 2| ≤ M) (hL₃ : |L 3 - P 3| ≤ M) :
    |liftAffine L v 2 + liftAffine L v 3 * t - liftAffine P v 2 - liftAffine P v 3 * t| ≤ 3 * M ∧
      |liftAffine L v 4 + liftAffine L v 5 * t - liftAffine P v 4 - liftAffine P v 5 * t| ≤ 3 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hL₂
  have hterm : |t * (L 3 - P 3)| ≤ 2 * M := by
    rw [abs_mul]
    exact mul_le_mul ht hL₃ (abs_nonneg _) (by norm_num)
  constructor
  · have hid : liftAffine L v 2 + liftAffine L v 3 * t -
        liftAffine P v 2 - liftAffine P v 3 * t = (L 2 - P 2) - t * (L 3 - P 3) := by
      simp only [liftAffine, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  · simpa only [liftAffine, Matrix.cons_val, Matrix.head_cons, zero_mul, add_zero, sub_zero]
      using hL₃.trans (show M ≤ 3 * M by linarith)

/-- Each fine native entry supplies one scalar support center in a raw chart.
The parent-child gradient error is paid across the original static square;
the reconstruction error uses only the original velocity/contact defect. -/
theorem normalizedResidual_original_child_error (L P : Fin 4 → ℝ) (h b : Fin 6 → ℝ)
    {v t D a₀ a₁ p₀ q₀ K χ Mc Md : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hD : 0 < D) (ha₀ : 0 < a₀)
    (hvel : |b 3 - v| ≤ χ) (hdef : |b 4 + b 0| ≤ χ)
    (hLs₂ : |L 2| ≤ Mc) (hLs₃ : |L 3| ≤ Mc)
    (hdiff₂ : |L 2 - P 2| ≤ Md) (hdiff₃ : |L 3 - P 3| ≤ Md)
    (hp : |b 0 - p₀| ≤ D) (hq : |b 1 - q₀| ≤ D)
    (hfit : |b 2 + t * b 5 - (L 0 + L 1 * t + L 2 * (b 0 + t * b 3) +
      L 3 * (b 1 + t * b 4))| ≤ K * a₁) :
    |normalizedResidual (liftAffine P v) h D a₀ p₀ q₀ t (b 0) (b 1) (b 2 + t * b 5) -
      (predictor (liftAffine L v) t p₀ q₀ - predictor h t p₀ q₀) / a₀| ≤
        (K * a₁ + 2 * Mc * χ + 6 * Md * D) / a₀ := by
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hvel
  have hMd : 0 ≤ Md := (abs_nonneg _).trans hdiff₂
  have hfit' : |b 2 + t * b 5 - predictor (liftAffine L v) t (b 0) (b 1)| ≤
      K * a₁ + 2 * Mc * χ := by
    have hf := affine_fit_to_parameter ht hdef hvel hfit
    exact hf.trans (by nlinarith [mul_le_mul_of_nonneg_right hLs₂ hχ,
      mul_le_mul_of_nonneg_right hLs₃ hχ])
  have ht2 : |t| ≤ 2 := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
  have hgrad := liftAffine_difference_gradients L P v ht2 hdiff₂ hdiff₃
  have he := normalizedResidual_child_error (f := liftAffine P v) (g := liftAffine L v)
    (h := h) hD ha₀ (by positivity : 0 ≤ 3 * Md) hp hq hfit' hgrad
  simpa only [show 2 * (3 * Md) * D = 6 * Md * D by ring] using he

end Submission.Obl.k4_horizontal_strict_parameter_step
