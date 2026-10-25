/- Adapted from: here:o009
Original marginal averaging proofs developed in this workspace. -/

import Submission.Lib.K4ModelReduction.BaseCellAveraging
import Submission.Lib.K4ModelReduction.BaseCellMass

/-! Mesh redistribution commutes with integrating hidden parameters.
The marginal need not itself have a polynomial sign-table representation. -/

namespace Submission.Lib.K4MarginalAveraging

open MeasureTheory
open scoped ENNReal
open Submission.Lib.K4ModelReduction

theorem meshLinAverage_lintegral {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SFinite μ] (f : Y → ℝ → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f))
    {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    meshLinAverage (fun t => ∫⁻ y, f y t ∂μ) ρ x =
      ∫⁻ y, meshLinAverage (f y) ρ x ∂μ := by
  unfold meshLinAverage
  calc
    _ = (ENNReal.ofReal ρ)⁻¹ *
        ∫⁻ y, ∫⁻ t : ℝ in halfOpenMeshCell ρ x, f y t ∂volume ∂μ := by
      congr 1
      exact (lintegral_lintegral_swap hf.aemeasurable).symm
    _ = _ := (lintegral_const_mul' _ _
      (ENNReal.inv_ne_top.mpr (by positivity))).symm

theorem meshAverage_integral_of_integrable {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SFinite μ] (f : Y → ℝ → ℝ) (ρ x : ℝ)
    (hf : Integrable (Function.uncurry f)
      (μ.prod (ProbabilityTheory.cond volume (meshCell ρ x)))) :
    meshAverage (fun t => ∫ y, f y t ∂μ) ρ x =
      ∫ y, meshAverage (f y) ρ x ∂μ :=
  (integral_integral_swap hf).symm

theorem meshAverage_integral {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (f : Y → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f))
    (M : ℝ) (hbound : ∀ y x, |f y x| ≤ M)
    {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    meshAverage (fun t => ∫ y, f y t ∂μ) ρ x =
      ∫ y, meshAverage (f y) ρ x ∂μ := by
  have := meshCell_law_isProbabilityMeasure hρ x
  have hint : Integrable (Function.uncurry f)
      (μ.prod (ProbabilityTheory.cond volume (meshCell ρ x))) :=
    Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => by
        change |f z.1 z.2| ≤ M
        exact hbound z.1 z.2)
  exact meshAverage_integral_of_integrable μ f ρ x hint

theorem marginal_abs_sub_integral_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f g : Y → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    ENNReal.ofReal |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| ≤
      ∫⁻ y, ENNReal.ofReal |f y - g y| ∂μ := by
  rw [← integral_sub hf hg]
  simpa only [Real.enorm_eq_ofReal_abs] using
    enorm_integral_le_lintegral_enorm (fun y => f y - g y)

/-- Integrating out hidden parameters contracts the full L1 discrepancy.
The outer integral is allowed to be infinite. -/
theorem marginal_lintegral_abs_sub_le {Y X : Type*}
    [MeasurableSpace Y] [MeasurableSpace X]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f g : Y → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfi : ∀ x, Integrable (fun y => f y x) μ)
    (hgi : ∀ x, Integrable (fun y => g y x) μ) :
    (∫⁻ x, ENNReal.ofReal |(∫ y, f y x ∂μ) - ∫ y, g y x ∂μ| ∂ν) ≤
      ∫⁻ z : Y × X, ENNReal.ofReal |f z.1 z.2 - g z.1 z.2| ∂μ.prod ν := by
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal |f y x - g y x| ∂μ ∂ν :=
      lintegral_mono fun x => marginal_abs_sub_integral_le μ _ _ (hfi x) (hgi x)
    _ = _ :=
      (lintegral_prod_symm _
        (ENNReal.measurable_ofReal.comp (hf.sub hg).abs).aemeasurable).symm

theorem meshAverage_marginal_error_pointwise {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (f : Y → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f))
    (M : ℝ) (hbound : ∀ y x, |f y x| ≤ M)
    {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    ENNReal.ofReal |meshAverage (fun t => ∫ y, f y t ∂μ) ρ x - ∫ y, f y x ∂μ| ≤
      ∫⁻ y, ENNReal.ofReal |meshAverage (f y) ρ x - f y x| ∂μ := by
  rw [meshAverage_integral μ f hf M hbound hρ]
  apply marginal_abs_sub_integral_le
  · exact Integrable.of_bound
      ((meshAverage_measurable f hf hρ).comp
        (measurable_id.prodMk measurable_const)).stronglyMeasurable.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using meshAverage_abs_le (f y) hρ (hbound y) x)
  · exact Integrable.of_bound hf.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using hbound y x)

/-- The observation-marginal averaging error is no larger than the error
of averaging the jointly measurable raw fibers. -/
theorem meshAverage_marginal_error_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (f : Y → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f))
    (M : ℝ) (hbound : ∀ y x, |f y x| ≤ M)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      |meshAverage (fun t => ∫ y, f y t ∂μ) ρ x - ∫ y, f y x ∂μ|) ≤
      ∫⁻ z : Y × ℝ, ENNReal.ofReal
        |meshAverage (f z.1) ρ z.2 - f z.1 z.2| ∂μ.prod volume := by
  calc
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y, ENNReal.ofReal
        |meshAverage (f y) ρ x - f y x| ∂μ :=
      lintegral_mono (meshAverage_marginal_error_pointwise μ f hf M hbound hρ)
    _ = _ :=
      (lintegral_prod_symm _ (ENNReal.measurable_ofReal.comp
        (((meshAverage_measurable f hf hρ).sub hf).abs)).aemeasurable).symm

/-- Polynomial control is needed only before taking the hidden marginal. -/
theorem polynomial_meshAverage_marginal_error_le {Y ι : Type*}
    [MeasurableSpace Y] [Fintype ι]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (p : Y → ι → Polynomial ℝ) (f : Y → ℝ → ℝ) (M : ℝ) (D : ℕ)
    (hf : Measurable (Function.uncurry f))
    (hM : 0 ≤ M) (hbound : ∀ y x, |f y x| ≤ M)
    (hdepend : ∀ y x x', (∀ i, (p y i).eval x ≤ 0 ↔ (p y i).eval x' ≤ 0) →
      f y x = f y x')
    (hdegree : ∀ y, ∑ i, (p y i).natDegree ≤ D)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      |meshAverage (fun t => ∫ y, f y t ∂μ) ρ x - ∫ y, f y x ∂μ|) ≤
      ENNReal.ofReal (4 * M * (D : ℝ) * ρ) * μ Set.univ :=
  (meshAverage_marginal_error_le μ f hf M hbound hρ).trans
    (polynomial_cell_averaging_product μ p f M D hf hM hbound hdepend hdegree hρ)

end Submission.Lib.K4MarginalAveraging
