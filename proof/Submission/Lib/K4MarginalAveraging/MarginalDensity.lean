/- Adapted from: here:o009
Original hidden-marginal averaging proofs developed in this workspace. -/

import Submission.Lib.K4MarginalAveraging.MarginalAveraging

/-! Exact observation marginals of product-density laws. -/

namespace Submission.Lib.K4MarginalAveraging

open MeasureTheory
open scoped ENNReal
open Submission.Lib.K4ModelReduction

/-- The density of a projection is its hidden-parameter integral. -/
theorem map_snd_withDensity_lintegral {Y X : Type*}
    [MeasurableSpace Y] [MeasurableSpace X]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f : Y → X → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    ((μ.prod ν).withDensity (Function.uncurry f)).map Prod.snd =
      ν.withDensity (fun x => ∫⁻ y, f y x ∂μ) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hφsnd : Measurable (fun z : Y × X => φ z.2) := hφ.comp measurable_snd
  rw [lintegral_map hφ measurable_snd]
  calc
    _ = ∫⁻ z : Y × X, f z.1 z.2 * φ z.2 ∂μ.prod ν :=
      lintegral_withDensity_eq_lintegral_mul _ hf hφsnd
    _ = ∫⁻ x, ∫⁻ y, f y x * φ x ∂μ ∂ν :=
      lintegral_prod_symm _ (hf.mul (hφ.comp measurable_snd)).aemeasurable
    _ = ∫⁻ x, (∫⁻ y, f y x ∂μ) * φ x ∂ν :=
      lintegral_congr fun x => lintegral_mul_const _ hf.of_uncurry_right
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ hf.lintegral_prod_left hφ).symm

/-- Bounded real nonnegative fibers give the same actual marginal law. -/
theorem map_snd_withDensity_integral {Y X : Type*}
    [MeasurableSpace Y] [MeasurableSpace X]
    (μ : Measure Y) (ν : Measure X) [IsFiniteMeasure μ] [SFinite ν]
    (f : Y → X → ℝ) (hf : Measurable (Function.uncurry f))
    (M : ℝ) (hbound : ∀ y x, |f y x| ≤ M) (hnonneg : ∀ y x, 0 ≤ f y x) :
    ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (f z.1 z.2))).map Prod.snd =
      ν.withDensity (fun x => ENNReal.ofReal (∫ y, f y x ∂μ)) := by
  calc
    _ = ν.withDensity (fun x => ∫⁻ y, ENNReal.ofReal (f y x) ∂μ) :=
      map_snd_withDensity_lintegral μ ν (fun y x => ENNReal.ofReal (f y x))
        (ENNReal.measurable_ofReal.comp hf)
    _ = _ := by
      congr 1
      funext x
      apply Eq.symm
      apply ofReal_integral_eq_lintegral_ofReal
      · exact Integrable.of_bound hf.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable M
          (Filter.Eventually.of_forall fun y => by
            simpa only [Real.norm_eq_abs] using hbound y x)
      · exact Filter.Eventually.of_forall fun y => hnonneg y x

end Submission.Lib.K4MarginalAveraging
