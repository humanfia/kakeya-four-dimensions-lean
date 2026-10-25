/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/PredictorBounds.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Lib.K4FullTimeLayers.Geometry
import Submission.Obl.k4_horizontal_strict_parameter_step.ReconstructionMesh
import Submission.Obl.k4_horizontal_strict_parameter_step.NormalizedResidual

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set

/-- The whole-square norm already carried by a full-time label controls its
static-parameter gradients at every time. -/
theorem predictor_gradients {h : Fin 6 → ℝ} {p₀ q₀ D M t : ℝ} (hD : 0 < D)
    (hbound : ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |predictor h t p q| ≤ M) :
    |h 2 + h 3 * t| ≤ 2 * M / D ∧ |h 4 + h 5 * t| ≤ 2 * M / D := by
  have hp : p₀ ∈ Icc p₀ (p₀ + D) := ⟨le_rfl, by linarith⟩
  have hq : q₀ ∈ Icc q₀ (q₀ + D) := ⟨le_rfl, by linarith⟩
  exact Submission.Lib.K4FullTimeLayers.affine_square_slopes hD
    (hbound p₀ hp q₀ hq) (hbound (p₀ + D) ⟨by linarith, le_rfl⟩ q₀ hq)
    (hbound p₀ hp (q₀ + D) ⟨by linarith, le_rfl⟩)

/-- At a parameter point inside the old square, the same full-time norm bounds
the time slope. No raw coefficient bound is needed for mesh reconstruction. -/
theorem predictor_timeSlope_bound {h : Fin 6 → ℝ} {p q M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |predictor h t p q| ≤ M) :
    |predictorTimeSlope h p q| ≤ 2 * M := by
  have h0 := hbound 0 (by norm_num)
  have h1 := hbound 1 (by norm_num)
  have heq : predictorTimeSlope h p q = predictor h 1 p q - predictor h 0 p q := by
    dsimp [predictorTimeSlope, predictor]; ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

/-- Whole-domain comparison of a true entry with the baseline predictor gives
the bounded row required by scalar normalization. -/
theorem normalizedRow_bound {f h : Fin 6 → ℝ} {p₀ q₀ D a M t : ℝ}
    (hD : 0 < D) (ha : 0 < a)
    (hbound : ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |predictor f t p q - predictor h t p q| ≤ M * a) :
    ∀ i, |normalizedRow f h D a t i| ≤ 2 * M := by
  let g : Fin 6 → ℝ := fun i => f i - h i
  have hnorm : ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |predictor g t p q| ≤ M * a := by
    intro p hp q hq
    have heq : predictor g t p q = predictor f t p q - predictor h t p q := by
      dsimp [g, predictor]; ring
    rw [heq]
    exact hbound p hp q hq
  obtain ⟨h1, h2⟩ := predictor_gradients hD hnorm
  have hs (v : ℝ) (hv : |v| ≤ 2 * (M * a) / D) : |D / a * v| ≤ 2 * M := by
    rw [abs_mul, abs_of_pos (div_pos hD ha)]
    calc
      _ ≤ D / a * (2 * (M * a) / D) := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = _ := by field_simp <;> ring
  intro i
  fin_cases i
  · change |D / a * (f 2 + f 3 * t - h 2 - h 3 * t)| ≤ 2 * M
    apply hs
    convert h1 using 1 <;> dsimp [g] <;> congr 1 <;> ring
  · change |D / a * (f 4 + f 5 * t - h 4 - h 5 * t)| ≤ 2 * M
    apply hs
    convert h2 using 1 <;> dsimp [g] <;> congr 1 <;> ring

/-- Endpoint bounds control an affine row on the padded time interval. -/
theorem affine_row_extended {a b M t : ℝ} (ha : |a| ≤ M) (hb : |a + b| ≤ M)
    (ht : t ∈ Icc (-1 : ℝ) 2) : |a + b * t| ≤ 4 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans ha
  have ht0 : |t| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have ht1 : |1 - t| ≤ 2 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  calc
    _ = |(1 - t) * a + t * (a + b)| := by congr 1; ring
    _ ≤ |(1 - t) * a| + |t * (a + b)| := abs_add_le _ _
    _ ≤ 2 * M + 2 * M := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul ht1 ha (abs_nonneg _) (by norm_num))
        (mul_le_mul ht0 hb (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- The full-time whole-square norm also controls gradients at all nearby
jittered times, with no absolute raw coefficient bound. -/
theorem predictor_gradients_extended {h : Fin 6 → ℝ} {p₀ q₀ D M t : ℝ}
    (hD : 0 < D) (ht : t ∈ Icc (-1 : ℝ) 2)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |predictor h u p q| ≤ M) :
    |h 2 + h 3 * t| ≤ 8 * M / D ∧ |h 4 + h 5 * t| ≤ 8 * M / D := by
  have h0 := predictor_gradients hD (hbound 0 (by norm_num))
  have h1 := predictor_gradients hD (hbound 1 (by norm_num))
  simp only [mul_zero, add_zero] at h0
  simp only [mul_one] at h1
  constructor
  · exact (affine_row_extended h0.1 h1.1 ht).trans_eq (by ring)
  · exact (affine_row_extended h0.2 h1.2 ht).trans_eq (by ring)

end Submission.Obl.k4_horizontal_strict_parameter_step
