/- Adapted from: here:o009
Original marginal averaging proofs developed in this workspace. -/

import Submission.Lib.K4MarginalAveraging.MarginalDensity

/-! Explicit marginal densities retaining arbitrary countable labels. -/

namespace Submission.Lib.K4MarginalAveraging

open MeasureTheory Set
open scoped ENNReal

noncomputable def countedMarginal {Y X A : Type*}
    [MeasurableSpace Y] (μ : Measure Y)
    (f : Y → X → ℝ≥0∞) (L : Y × X → A) (z : X × A) : ℝ≥0∞ := by
  classical
  exact ∫⁻ y, if L (y, z.1) = z.2 then f y z.1 else 0 ∂μ

theorem countedMarginal_measurable {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) [SFinite μ]
    (f : Y → X → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (L : Y × X → A) (hL : Measurable L) :
    Measurable (countedMarginal μ f L) := by
  classical
  have heq : MeasurableSet {z : Y × (X × A) | L (z.1, z.2.1) = z.2.2} :=
    measurableSet_eq_fun
      (hL.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
      (measurable_snd.comp measurable_snd)
  have hF : Measurable (fun z : Y × (X × A) =>
      if L (z.1, z.2.1) = z.2.2 then f z.1 z.2.1 else 0) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).indicator heq
  exact hF.lintegral_prod_left

theorem lintegral_counted_test {Y A : Type*}
    [MeasurableSpace Y] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A] [DecidableEq A]
    (μ : Measure Y) [SFinite μ]
    (f : Y → ℝ≥0∞) (hf : Measurable f)
    (L : Y → A) (hL : Measurable L) (φ : A → ℝ≥0∞) :
    (∫⁻ a, (∫⁻ y, if L y = a then f y else 0 ∂μ) * φ a ∂Measure.count) =
      ∫⁻ y, f y * φ (L y) ∂μ := by
  have hφ : Measurable φ := measurable_of_countable φ
  have heq : MeasurableSet {z : Y × A | L z.1 = z.2} :=
    measurableSet_eq_fun (hL.comp measurable_fst) measurable_snd
  have hF : Measurable (fun z : Y × A =>
      if L z.1 = z.2 then f z.1 * φ z.2 else 0) :=
    Measurable.ite heq ((hf.comp measurable_fst).mul (hφ.comp measurable_snd)) measurable_const
  calc
    _ = ∫⁻ a, ∫⁻ y, (if L y = a then f y else 0) * φ a ∂μ ∂Measure.count := by
      apply lintegral_congr
      intro a
      exact (lintegral_mul_const _ (Measurable.ite
        (measurableSet_eq_fun hL measurable_const) hf measurable_const)).symm
    _ = ∫⁻ a, ∫⁻ y, (if L y = a then f y * φ a else 0) ∂μ ∂Measure.count := by
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro y
      split_ifs <;> simp
    _ = ∫⁻ y, ∫⁻ a, (if L y = a then f y * φ a else 0) ∂Measure.count ∂μ :=
      (lintegral_lintegral_swap hF.aemeasurable).symm
    _ = _ := by
      apply lintegral_congr
      intro y
      rw [lintegral_count]
      calc
        _ = (if L y = L y then f y * φ (L y) else 0) :=
          tsum_eq_single (L y) (fun a ha => by simp [Ne.symm ha])
        _ = _ := ite_eq_left rfl

/-- Exact density formula for the joint continuous/discrete observation.
The labels can depend measurably on every raw coordinate. -/
theorem map_counted_withDensity {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f : Y → X → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (L : Y × X → A) (hL : Measurable L) :
    ((μ.prod ν).withDensity (Function.uncurry f)).map (fun z => (z.2, L z)) =
      (ν.prod Measure.count).withDensity (countedMarginal μ f L) := by
  classical
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hobs : Measurable (fun z : Y × X => (z.2, L z)) := measurable_snd.prodMk hL
  have hφobs : Measurable (fun z : Y × X => φ (z.2, L z)) := hφ.comp hobs
  rw [lintegral_map hφ hobs]
  calc
    _ = ∫⁻ z : Y × X, f z.1 z.2 * φ (z.2, L z) ∂μ.prod ν :=
      lintegral_withDensity_eq_lintegral_mul _ hf hφobs
    _ = ∫⁻ x, ∫⁻ y, f y x * φ (x, L (y, x)) ∂μ ∂ν :=
      lintegral_prod_symm _ (hf.mul hφobs).aemeasurable
    _ = ∫⁻ x, ∫⁻ a, countedMarginal μ f L (x, a) * φ (x, a) ∂Measure.count ∂ν := by
      apply lintegral_congr
      intro x
      exact (lintegral_counted_test μ (fun y => f y x) hf.of_uncurry_right
        (fun y => L (y, x)) (hL.comp (measurable_id.prodMk measurable_const))
        (fun a => φ (x, a))).symm
    _ = ∫⁻ z : X × A, countedMarginal μ f L z * φ z ∂ν.prod Measure.count :=
      (lintegral_prod _ ((countedMarginal_measurable μ f hf L hL).mul hφ).aemeasurable).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _
      (countedMarginal_measurable μ f hf L hL) hφ).symm

noncomputable def realCountedMarginal {Y X A : Type*}
    [MeasurableSpace Y] (μ : Measure Y)
    (f : Y → X → ℝ) (L : Y × X → A) (z : X × A) : ℝ := by
  classical
  exact ∫ y, if L (y, z.1) = z.2 then f y z.1 else 0 ∂μ

theorem realCountedMarginal_measurable {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) [SFinite μ]
    (f : Y → X → ℝ) (hf : Measurable (Function.uncurry f))
    (L : Y × X → A) (hL : Measurable L) :
    Measurable (realCountedMarginal μ f L) := by
  classical
  have heq : MeasurableSet {z : Y × (X × A) | L (z.1, z.2.1) = z.2.2} :=
    measurableSet_eq_fun
      (hL.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
      (measurable_snd.comp measurable_snd)
  have hF : Measurable (fun z : Y × (X × A) =>
      if L (z.1, z.2.1) = z.2.2 then f z.1 z.2.1 else 0) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).indicator heq
  exact hF.stronglyMeasurable.integral_prod_left'.measurable

theorem ofReal_realCountedMarginal_of_integrable {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (f : Y → X → ℝ)
    (L : Y × X → A) (hL : Measurable L)
    (hfi : ∀ x, Integrable (fun y => f y x) μ) (hnonneg : ∀ y x, 0 ≤ f y x)
    (z : X × A) :
    ENNReal.ofReal (realCountedMarginal μ f L z) =
      countedMarginal μ (fun y x => ENNReal.ofReal (f y x)) L z := by
  classical
  have hint : Integrable (fun y => if L (y, z.1) = z.2 then f y z.1 else 0) μ := by
    exact (hfi z.1).indicator
      (measurableSet_eq_fun (hL.comp (measurable_id.prodMk measurable_const)) measurable_const)
  rw [realCountedMarginal, ofReal_integral_eq_lintegral_ofReal hint]
  · apply lintegral_congr
    intro y
    by_cases hy : L (y, z.1) = z.2 <;> simp only [hy, ↓reduceIte, ENNReal.ofReal_zero]
  · exact Filter.Eventually.of_forall fun y => by
      change 0 ≤ if L (y, z.1) = z.2 then f y z.1 else 0
      split_ifs <;> first | exact hnonneg y z.1 | exact le_rfl

theorem ofReal_realCountedMarginal {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (f : Y → X → ℝ) (hf : Measurable (Function.uncurry f))
    (L : Y × X → A) (hL : Measurable L)
    (M : ℝ) (hbound : ∀ y x, |f y x| ≤ M) (hnonneg : ∀ y x, 0 ≤ f y x)
    (z : X × A) :
    ENNReal.ofReal (realCountedMarginal μ f L z) =
      countedMarginal μ (fun y x => ENNReal.ofReal (f y x)) L z := by
  apply ofReal_realCountedMarginal_of_integrable μ f L hL _ hnonneg z
  intro x
  exact Integrable.of_bound hf.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y =>
      show ‖f y x‖ ≤ M by simpa only [Real.norm_eq_abs] using hbound y x)

theorem map_counted_withDensity_real_of_integrable {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f : Y → X → ℝ) (hf : Measurable (Function.uncurry f))
    (L : Y × X → A) (hL : Measurable L)
    (hfi : ∀ x, Integrable (fun y => f y x) μ) (hnonneg : ∀ y x, 0 ≤ f y x) :
    ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (f z.1 z.2))).map
      (fun z => (z.2, L z)) =
      (ν.prod Measure.count).withDensity (fun z => ENNReal.ofReal (realCountedMarginal μ f L z)) := by
  calc
    _ = (ν.prod Measure.count).withDensity
        (countedMarginal μ (fun y x => ENNReal.ofReal (f y x)) L) :=
      map_counted_withDensity μ ν (fun y x => ENNReal.ofReal (f y x))
        (ENNReal.measurable_ofReal.comp hf) L hL
    _ = _ := by
      congr 1
      funext z
      exact (ofReal_realCountedMarginal_of_integrable μ f L hL hfi hnonneg z).symm

theorem map_counted_withDensity_real {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (ν : Measure X) [IsFiniteMeasure μ] [SFinite ν]
    (f : Y → X → ℝ) (hf : Measurable (Function.uncurry f))
    (L : Y × X → A) (hL : Measurable L)
    (M : ℝ) (hbound : ∀ y x, |f y x| ≤ M) (hnonneg : ∀ y x, 0 ≤ f y x) :
    ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (f z.1 z.2))).map
      (fun z => (z.2, L z)) =
      (ν.prod Measure.count).withDensity (fun z => ENNReal.ofReal (realCountedMarginal μ f L z)) := by
  apply map_counted_withDensity_real_of_integrable μ ν f hf L hL _ hnonneg
  intro x
  exact Integrable.of_bound hf.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y =>
      show ‖f y x‖ ≤ M by simpa only [Real.norm_eq_abs] using hbound y x)

/-- The joint marginal contracts L1 discrepancy without a factor in the
number of possible observation labels. -/
theorem counted_marginal_lintegral_abs_sub_le {Y X A : Type*}
    [MeasurableSpace Y] [MeasurableSpace X] [MeasurableSpace A]
    [Countable A] [MeasurableSingletonClass A]
    (μ : Measure Y) (ν : Measure X) [SFinite μ] [SFinite ν]
    (f g : Y → X → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfi : ∀ x, Integrable (fun y => f y x) μ)
    (hgi : ∀ x, Integrable (fun y => g y x) μ)
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
    apply marginal_lintegral_abs_sub_le μ (ν.prod Measure.count) F G hF hG
    · intro z
      exact (hfi z.1).indicator (measurableSet_eq_fun
        (hL.comp (measurable_id.prodMk measurable_const)) measurable_const)
    · intro z
      exact (hgi z.1).indicator (measurableSet_eq_fun
        (hL.comp (measurable_id.prodMk measurable_const)) measurable_const)
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
