import Submission.Obl.k4_remainder_pure_profile_normalization.DensityFactor

namespace Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
open MeasureTheory
open scoped ENNReal

/-- The conditioned incidence budget cancels its factor in the world weight. -/
theorem normalized_weight_factor {w a q Z : ℝ} (hw : 0 ≤ w) (ha : 0 < a)
    (hq : 0 < q) (hZ : 0 < Z) :
    ENNReal.ofReal (w * (a * q) / Z) *
      (ENNReal.ofReal a * ENNReal.ofReal q)⁻¹ =
      ENNReal.ofReal Z⁻¹ * ENNReal.ofReal w := by
  rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_inv_of_pos (mul_pos ha hq),
    ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hw (mul_pos ha hq).le) hZ.le),
    ← ENNReal.ofReal_mul (inv_pos.mpr hZ).le]
  congr 1
  field_simp

namespace Frame
variable (F : Frame)

/-- Weighted normalized exceptional masses equal the original selected masses
with the single common normalizing factor. -/
theorem normalized_weighted_mass (hq : 0 < F.q) (hD : IsUnit F.D.det)
    (ν : Measure Trajectory) [IsFiniteMeasure ν] {A₀ : Set Trajectory} {E : Set Incidence}
    (hA : MeasurableSet A₀) (hE : MeasurableSet E)
    (hsub : ∀ p ∈ E, p.1 ∈ A₀ ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q))
    (ha : 0 < (ν A₀).toReal) {w Z : ℝ} (hw : 0 ≤ w) (hZ : 0 < Z)
    (S : Set Incidence) (hS : MeasurableSet S) :
    ENNReal.ofReal (w * ((ν A₀).toReal * F.q) / Z) *
      ((((ν A₀)⁻¹ • (ν.restrict A₀).map F.normTraj).prod volume).restrict
        (F.normEvent A₀ E)) S =
      ENNReal.ofReal Z⁻¹ * ENNReal.ofReal w *
        ((ν.prod volume).restrict E) (F.normInc ⁻¹' S) := by
  rw [F.normalized_selected_law hq hD ν hA hE hsub,
    Measure.smul_apply, smul_eq_mul, Measure.map_apply F.measurable_normInc hS,
    ← mul_assoc]
  congr 1
  simpa only [ENNReal.ofReal_toReal (measure_ne_top ν A₀)] using
    normalized_weight_factor hw ha hq hZ

end Frame
end Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
