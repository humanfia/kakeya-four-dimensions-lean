/- Adapted from: here:o009
Original almost-everywhere marginal and measurable L1 contraction proofs developed in this workspace. -/

import Submission.Lib.K4MarginalAveraging.CountedMarginal

/-! Real marginal formulas under almost-everywhere fiber integrability. -/

namespace Submission.Lib.K4MarginalAveraging

open MeasureTheory
open scoped ENNReal

/-- The extended real-valued integral remains a contraction in L1 even
at divergent fibers: finite L1 difference forces the two fibers to have
the same integrability status. -/
theorem marginal_abs_sub_integral_le_of_measurable {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f g : Y → ℝ) (hf : Measurable f) (hg : Measurable g) :
    ENNReal.ofReal |(∫ y, f y ∂μ) - ∫ y, g y ∂μ| ≤
      ∫⁻ y, ENNReal.ofReal |f y - g y| ∂μ := by
  by_cases htop : (∫⁻ y, ENNReal.ofReal |f y - g y| ∂μ) = ∞
  · rw [htop]
    exact le_top
  have hdiff : Integrable (fun y => f y - g y) μ := by
    refine ⟨(hf.sub hg).stronglyMeasurable.aestronglyMeasurable, ?_⟩
    simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using
      (lt_top_iff_ne_top.mpr htop)
  by_cases hfi : Integrable f μ
  · have hgi : Integrable g μ := by
      convert hfi.sub hdiff using 1
      funext y
      change g y = f y - (f y - g y)
      ring
    exact marginal_abs_sub_integral_le μ f g hfi hgi
  · have hgi : ¬ Integrable g μ := by
      intro hgi
      apply hfi
      convert hdiff.add hgi using 1
      funext y
      change f y = (f y - g y) + g y
      ring
    rw [integral_undef hfi, integral_undef hgi, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact zero_le

theorem marginal_lintegral_abs_sub_le_of_measurable {Y X : Type*}
    [MeasurableSpace Y] [MeasurableSpace X]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f g : Y → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    (∫⁻ x, ENNReal.ofReal |(∫ y, f y x ∂μ) - ∫ y, g y x ∂μ| ∂ν) ≤
      ∫⁻ z : Y × X, ENNReal.ofReal |f z.1 z.2 - g z.1 z.2| ∂μ.prod ν := by
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal |f y x - g y x| ∂μ ∂ν :=
      lintegral_mono fun x => marginal_abs_sub_integral_le_of_measurable μ _ _
        hf.of_uncurry_right hg.of_uncurry_right
    _ = _ := (lintegral_prod_symm _
      (ENNReal.measurable_ofReal.comp (hf.sub hg).abs).aemeasurable).symm

theorem ofReal_realCountedMarginal_of_integrable_fiber {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (f : Y → X → ℝ)
    (L : Y × X → A) (hL : Measurable L)
    (hnonneg : ∀ y x, 0 ≤ f y x) (z : X × A)
    (hfi : Integrable (fun y => f y z.1) μ) :
    ENNReal.ofReal (realCountedMarginal μ f L z) =
      countedMarginal μ (fun y x => ENNReal.ofReal (f y x)) L z := by
  classical
  have hint : Integrable (fun y => if L (y, z.1) = z.2 then f y z.1 else 0) μ :=
    hfi.indicator (measurableSet_eq_fun
      (hL.comp (measurable_id.prodMk measurable_const)) measurable_const)
  rw [realCountedMarginal, ofReal_integral_eq_lintegral_ofReal hint]
  · apply lintegral_congr
    intro y
    by_cases hy : L (y, z.1) = z.2 <;> simp only [hy, ↓reduceIte, ENNReal.ofReal_zero]
  · exact Filter.Eventually.of_forall fun y => by
      change 0 ≤ if L (y, z.1) = z.2 then f y z.1 else 0
      split_ifs <;> first | exact hnonneg y z.1 | exact le_rfl

/-- A null set of divergent hidden fibers does not alter the observation
law. This version needs only almost-everywhere fiber integrability. -/
theorem map_counted_withDensity_real_of_ae_integrable {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f : Y → X → ℝ) (hf : Measurable (Function.uncurry f))
    (L : Y × X → A) (hL : Measurable L)
    (hfi : ∀ᵐ x ∂ν, Integrable (fun y => f y x) μ)
    (hnonneg : ∀ y x, 0 ≤ f y x) :
    ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (f z.1 z.2))).map
      (fun z => (z.2, L z)) =
      (ν.prod Measure.count).withDensity (fun z => ENNReal.ofReal (realCountedMarginal μ f L z)) := by
  calc
    _ = (ν.prod Measure.count).withDensity
        (countedMarginal μ (fun y x => ENNReal.ofReal (f y x)) L) :=
      map_counted_withDensity μ ν (fun y x => ENNReal.ofReal (f y x))
        (ENNReal.measurable_ofReal.comp hf) L hL
    _ = _ := by
      apply withDensity_congr_ae
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
        (countedMarginal_measurable μ (fun y x => ENNReal.ofReal (f y x))
          (ENNReal.measurable_ofReal.comp hf) L hL)
        (ENNReal.measurable_ofReal.comp (realCountedMarginal_measurable μ f hf L hL)))).mpr
      filter_upwards [hfi] with x hx
      exact Filter.Eventually.of_forall fun a =>
        (ofReal_realCountedMarginal_of_integrable_fiber μ f L hL hnonneg (x, a) hx).symm

theorem map_counted_withDensity_real_of_integrable_product {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f : Y → X → ℝ) (hf : Measurable (Function.uncurry f))
    (L : Y × X → A) (hL : Measurable L)
    (hfi : Integrable (Function.uncurry f) (μ.prod ν))
    (hnonneg : ∀ y x, 0 ≤ f y x) :
    ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (f z.1 z.2))).map
      (fun z => (z.2, L z)) =
      (ν.prod Measure.count).withDensity (fun z => ENNReal.ofReal (realCountedMarginal μ f L z)) :=
  map_counted_withDensity_real_of_ae_integrable μ ν f hf L hL hfi.prod_left_ae hnonneg

theorem integrable_of_lintegral_abs_sub_lt_top {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f g : Y → ℝ) (hf : Measurable f) (hgi : Integrable g μ)
    (hclose : (∫⁻ y, ENNReal.ofReal |f y - g y| ∂μ) < ∞) : Integrable f μ := by
  have hdiff : Integrable (fun y => f y - g y) μ := by
    refine ⟨hf.stronglyMeasurable.aestronglyMeasurable.sub hgi.aestronglyMeasurable, ?_⟩
    simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] using hclose
  convert hdiff.add hgi using 1
  funext y
  change f y = (f y - g y) + g y
  ring

/-- Finite global L1 error relative to an integrable approximation is
enough for the actual real marginal law; exceptional divergent fibers
need no pointwise repair. -/
theorem map_counted_withDensity_real_of_l1_close {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f g : Y → X → ℝ) (hf : Measurable (Function.uncurry f))
    (hgi : Integrable (Function.uncurry g) (μ.prod ν))
    (hclose : (∫⁻ z : Y × X, ENNReal.ofReal |f z.1 z.2 - g z.1 z.2| ∂μ.prod ν) < ∞)
    (L : Y × X → A) (hL : Measurable L) (hnonneg : ∀ y x, 0 ≤ f y x) :
    ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (f z.1 z.2))).map
      (fun z => (z.2, L z)) =
      (ν.prod Measure.count).withDensity (fun z => ENNReal.ofReal (realCountedMarginal μ f L z)) :=
  map_counted_withDensity_real_of_integrable_product μ ν f hf L hL
    (integrable_of_lintegral_abs_sub_lt_top (μ.prod ν) _ _ hf hgi hclose) hnonneg

theorem counted_marginal_lintegral_abs_sub_le_of_measurable {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f g : Y → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (L : Y × X → A) (hL : Measurable L) :
    (∫⁻ z : X × A, ENNReal.ofReal
      |realCountedMarginal μ f L z - realCountedMarginal μ g L z| ∂ν.prod Measure.count) ≤
      ∫⁻ z : Y × X, ENNReal.ofReal |f z.1 z.2 - g z.1 z.2| ∂μ.prod ν := by
  classical
  let F : Y → (X × A) → ℝ :=
    fun y z => if L (y, z.1) = z.2 then f y z.1 else 0
  let G : Y → (X × A) → ℝ :=
    fun y z => if L (y, z.1) = z.2 then g y z.1 else 0
  have heq : MeasurableSet {z : Y × (X × A) | L (z.1, z.2.1) = z.2.2} :=
    measurableSet_eq_fun
      (hL.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
      (measurable_snd.comp measurable_snd)
  have hF : Measurable (Function.uncurry F) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).indicator heq
  have hG : Measurable (Function.uncurry G) :=
    (hg.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).indicator heq
  have hE : Measurable (fun z : Y × (X × A) =>
      ENNReal.ofReal |F z.1 z.2 - G z.1 z.2|) :=
    ENNReal.measurable_ofReal.comp (hF.sub hG).abs
  have hcontraction : (∫⁻ z : X × A, ENNReal.ofReal
      |realCountedMarginal μ f L z - realCountedMarginal μ g L z| ∂ν.prod Measure.count) ≤
      ∫⁻ z : Y × (X × A), ENNReal.ofReal |F z.1 z.2 - G z.1 z.2|
        ∂μ.prod (ν.prod Measure.count) := by
    exact marginal_lintegral_abs_sub_le_of_measurable μ (ν.prod Measure.count) F G hF hG
  apply hcontraction.trans_eq
  calc
    _ = ∫⁻ y, ∫⁻ x, ∫⁻ a, ENNReal.ofReal |F y (x, a) - G y (x, a)|
        ∂Measure.count ∂ν ∂μ := by
      rw [lintegral_prod _ hE.aemeasurable]
      apply lintegral_congr
      intro y
      exact lintegral_prod _ (hE.comp (measurable_const.prodMk measurable_id)).aemeasurable
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal |f y x - g y x| ∂ν ∂μ := by
      apply lintegral_congr
      intro y
      apply lintegral_congr
      intro x
      rw [lintegral_count]
      calc
        _ = ENNReal.ofReal |F y (x, L (y, x)) - G y (x, L (y, x))| :=
          tsum_eq_single (L (y, x)) (fun a ha => by simp [F, G, Ne.symm ha])
        _ = _ := by simp only [F, G, ↓reduceIte]
    _ = _ := (lintegral_prod _
      (ENNReal.measurable_ofReal.comp (hf.sub hg).abs).aemeasurable).symm

end Submission.Lib.K4MarginalAveraging
