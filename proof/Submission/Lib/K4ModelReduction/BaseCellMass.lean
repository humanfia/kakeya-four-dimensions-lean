import Submission.Lib.K4ModelReduction.CellMass

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Joint mass preservation and L1 contraction of mesh-cell averaging. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory
open scoped ENNReal

theorem meshAverage_product_mass {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f : Y → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f))
    (M : ℝ) (hbound : ∀ y x, |f y x| ≤ M) (hnonneg : ∀ y x, 0 ≤ f y x)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ z : Y × ℝ, ENNReal.ofReal (meshAverage (f z.1) ρ z.2) ∂μ.prod volume) =
      ∫⁻ z : Y × ℝ, ENNReal.ofReal (f z.1 z.2) ∂μ.prod volume := by
  rw [lintegral_prod (fun z : Y × ℝ => ENNReal.ofReal (meshAverage (f z.1) ρ z.2))
    (ENNReal.measurable_ofReal.comp
    (meshAverage_measurable f hf hρ)).aemeasurable,
    lintegral_prod (fun z : Y × ℝ => ENNReal.ofReal (f z.1 z.2))
      (ENNReal.measurable_ofReal.comp hf).aemeasurable]
  apply lintegral_congr
  intro y
  exact meshAverage_mass (f y) hf.of_uncurry_left M (hbound y) (hnonneg y) hρ

theorem meshAverage_product_abs_sub_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f g : Y → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (M L : ℝ) (hfbound : ∀ y x, |f y x| ≤ M) (hgbound : ∀ y x, |g y x| ≤ L)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ z : Y × ℝ, ENNReal.ofReal
      |meshAverage (f z.1) ρ z.2 - meshAverage (g z.1) ρ z.2| ∂μ.prod volume) ≤
      ∫⁻ z : Y × ℝ, ENNReal.ofReal |f z.1 z.2 - g z.1 z.2| ∂μ.prod volume := by
  rw [lintegral_prod (fun z : Y × ℝ => ENNReal.ofReal
      |meshAverage (f z.1) ρ z.2 - meshAverage (g z.1) ρ z.2|)
    (ENNReal.measurable_ofReal.comp
    (((meshAverage_measurable f hf hρ).sub (meshAverage_measurable g hg hρ)).abs)).aemeasurable,
    lintegral_prod (fun z : Y × ℝ => ENNReal.ofReal |f z.1 z.2 - g z.1 z.2|)
      (ENNReal.measurable_ofReal.comp (hf.sub hg).abs).aemeasurable]
  apply lintegral_mono
  intro y
  exact meshAverage_lintegral_abs_sub_le (f y) (g y) hf.of_uncurry_left hg.of_uncurry_left
    M L (hfbound y) (hgbound y) hρ

end Submission.Lib.K4ModelReduction
