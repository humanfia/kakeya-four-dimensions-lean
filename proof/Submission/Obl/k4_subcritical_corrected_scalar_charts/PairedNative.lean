/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/PairedNative.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.PairedInterface
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeLevel
import Submission.Obl.k4_subcritical_corrected_scalar_charts.DirectionalCorrection

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory MvPolynomial

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The paired cut's polynomial-defined native predictor is the very same
original affine entry stored by the full native atlas. -/
theorem NativeLevel.nativeParameter_eq {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s)) (v t p q : ℝ) :
    cfg.nativeParameter k s i v t p q = parameterPredictor (horizontalLift (a.L i) v) t p q := by
  unfold nativeParameter
  rw [a.defining_polynomial i, horizontalLift_eval]
  simp only [eval_sub, eval_X, eval_add, eval_C, eval_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Whole-square comparison gives the directional derivative comparison at
every time of that native block. -/
theorem NativeLevel.directional_comparison {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s))
    {v t p₀ q₀ D E : ℝ} {H : Fin 6 → ℝ} (hD : 0 < D) (ht : t ∈ Icc (0 : ℝ) 1)
    (hnorm : ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |cfg.nativeParameter k s i v t p q - predictor H t p q| ≤ E) :
    |fiberDerivative (horizontalLift (a.L i) v - H) t| ≤ 6 * E / D := by
  apply fiberDerivative_of_square_norm hD ht
  intro p hp q hq
  rw [parameterPredictor_sub]
  have hh := hnorm p hp q hq
  rw [a.nativeParameter_eq] at hh
  exact hh

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
