/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeScalarFit.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeScalarEntry
import Submission.Obl.k4_subcritical_corrected_scalar_charts.PairedNative

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Each genuine original fitted trajectory has the native parameter fit;
only its velocity-bin and horizontal reconstruction errors are added. -/
theorem NativeLevel.parameter_fit (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s)) {l : α} {v t χ : ℝ}
    (hl : l ∈ cfg.B k s i) (ht : t ∈ Icc (0 : ℝ) 1)
    (htI : t ∈ Submission.Obl.k4_critical_intercept_concentration.Data.I
      (cfg.T k s) (cfg.j k s i))
    (hvel : |cfg.b k l 3 - v| ≤ χ) (hhor : |cfg.b k l 4 + cfg.b k l 0| ≤ χ) :
    |cfg.b k l 2 + t * cfg.b k l 5 -
      parameterPredictor (horizontalLift (a.L i) v) t (cfg.b k l 0) (cfg.b k l 1)| ≤
        cfg.K k * cfg.N k ^ (-s) + 72 * cfg.K k ^ 4 * χ := by
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hvel
  have hh := Submission.Lib.K4FullTimeLayers.affine_fit_to_parameter ht hhor hvel
    (a.fit i l hl t htI)
  refine hh.trans ?_
  have h2 : |a.L i 2| ≤ 36 * cfg.K k ^ 4 := a.slope i 1
  have h3 : |a.L i 3| ≤ 36 * cfg.K k ^ 4 := a.slope i 2
  nlinarith [mul_le_mul_of_nonneg_right h2 hχ, mul_le_mul_of_nonneg_right h3 hχ]

/-- The actual original native fit descends to the corrected scalar entry.
The old fit scale and the contact-direction error remain separate. -/
theorem NativeLevel.corrected_scalar_fit (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s))
    (H : Fin 6 → ℝ) (β : Fin 3 → ℝ) {l : α} {D A p₀ q₀ v t χ η : ℝ}
    (hD : 0 < D) (hA : 0 < A) (hl : l ∈ cfg.B k s i)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (htI : t ∈ Submission.Obl.k4_critical_intercept_concentration.Data.I
      (cfg.T k s) (cfg.j k s i))
    (hvel : |cfg.b k l 3 - v| ≤ χ) (hhor : |cfg.b k l 4 + cfg.b k l 0| ≤ χ)
    (hcollapse : |nativeFiberSignal H (a.L i) D A t -
      (β 0 + β 1 * t + β 2 * t ^ 2)| ≤ η) :
    |(cfg.b k l 2 + t * cfg.b k l 5 -
        parameterPredictor H t (cfg.b k l 0) (cfg.b k l 1)) / A -
      parameterPredictor (fiberCorrection β) t ((cfg.b k l 0 - p₀) / D)
        ((cfg.b k l 1 - q₀) / D) -
      nativeScalarEntry H β (a.L i) D A p₀ q₀ v t
        ((cfg.b k l 1 - q₀) / D - 2 * t * ((cfg.b k l 0 - p₀) / D))| ≤
      (cfg.K k * cfg.N k ^ (-s) + 72 * cfg.K k ^ 4 * χ) / A +
        |(cfg.b k l 0 - p₀) / D| * η := by
  have hp : p₀ + D * ((cfg.b k l 0 - p₀) / D) = cfg.b k l 0 := by
    field_simp
    ring
  have hq : q₀ + D * ((cfg.b k l 1 - q₀) / D) = cfg.b k l 1 := by
    field_simp
    ring
  have hfit : |cfg.b k l 2 + t * cfg.b k l 5 -
      parameterPredictor (horizontalLift (a.L i) v) t
        (p₀ + D * ((cfg.b k l 0 - p₀) / D)) (q₀ + D * ((cfg.b k l 1 - q₀) / D))| ≤
        cfg.K k * cfg.N k ^ (-s) + 72 * cfg.K k ^ 4 * χ := by
    rw [hp, hq]
    exact a.parameter_fit h i hl ht htI hvel hhor
  have hh := nativeScalarEntry_fit H β (a.L i) hA hfit hcollapse
  simpa only [hp, hq] using hh

/-- Coarse whole-square comparison bounds the shared piecewise time signal,
independently of the displayed raw endpoint coefficient exponent. -/
theorem NativeLevel.coarse_signal_bound {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s))
    {v t p₀ q₀ D A E : ℝ} {H : Fin 6 → ℝ} (hD : 0 < D) (hA : 0 < A)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hnorm : ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |cfg.nativeParameter k s i v t p q - predictor H t p q| ≤ E) :
    |nativeFiberSignal H (a.L i) D A t| ≤ 6 * E / A := by
  have hh := a.directional_comparison i hD ht hnorm
  rw [fiberDerivative_sub, horizontalLift_fiberDerivative] at hh
  unfold nativeFiberSignal
  rw [abs_mul, abs_of_pos (div_pos hD hA)]
  apply (mul_le_mul_of_nonneg_left hh (div_pos hD hA).le).trans_eq
  field_simp

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
