import Submission.Lib.K4ModelReduction.BaseCellAveraging
import Submission.Lib.K4ModelReduction.CellConstancy

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Finite-support error bounds for polynomial base flattening. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Set
open scoped ENNReal

theorem polynomial_cell_averaging_supported_product
    {Y ι : Type*} [MeasurableSpace Y] [Fintype ι] (μ : Measure Y)
    (S : Set Y) (hS : MeasurableSet S)
    (p : Y → ι → Polynomial ℝ) (f : Y → ℝ → ℝ) (M : ℝ) (D : ℕ)
    (hf : Measurable (Function.uncurry f))
    (hM : 0 ≤ M) (hbound : ∀ y x, |f y x| ≤ M)
    (hsupport : ∀ y ∉ S, ∀ x, f y x = 0)
    (hdepend : ∀ y ∈ S, ∀ x x',
      (∀ i, (p y i).eval x ≤ 0 ↔ (p y i).eval x' ≤ 0) → f y x = f y x')
    (hdegree : ∀ y ∈ S, ∑ i, (p y i).natDegree ≤ D)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ z : Y × ℝ, ENNReal.ofReal |meshAverage (f z.1) ρ z.2 - f z.1 z.2| ∂μ.prod volume) ≤
      ENNReal.ofReal (4 * M * (D : ℝ) * ρ) * μ S := by
  classical
  have hG : Measurable (fun z : Y × ℝ =>
      ENNReal.ofReal |meshAverage (f z.1) ρ z.2 - f z.1 z.2|) :=
    ENNReal.measurable_ofReal.comp (((meshAverage_measurable f hf hρ).sub hf).abs)
  calc
    _ = ∫⁻ y, ∫⁻ x : ℝ, ENNReal.ofReal |meshAverage (f y) ρ x - f y x| ∂volume ∂μ :=
      lintegral_prod _ hG.aemeasurable
    _ ≤ ∫⁻ y, S.indicator (fun _ => ENNReal.ofReal (4 * M * (D : ℝ) * ρ)) y ∂μ := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy]
        have hd : ((∑ i, (p y i).natDegree : ℕ) : ℝ) ≤ (D : ℝ) := by
          exact_mod_cast hdegree y hy
        refine (polynomial_cell_averaging_error_bound (p y) (f y) M hM
          (hbound y) (hdepend y hy) hρ).trans (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hd (by positivity)) hρ.le
      · have hzero : f y = fun _ => 0 := funext (hsupport y hy)
        simp only [indicator_of_notMem hy, hzero, meshAverage, integral_zero,
          sub_self, abs_zero, ENNReal.ofReal_zero, lintegral_zero, le_refl]
    _ = _ := lintegral_indicator_const hS _

theorem averageInSplit_error_eq {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y × ℝ)
    (he : MeasurePreserving e μ (ν.prod volume)) (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (f : boundedMeasurableFunctions X M) :
    densityL1Distance μ (averageInSplit e M hρ f).val f.val =
      ∫⁻ z : Y × ℝ, ENNReal.ofReal
        |meshAverage (fun t => f.val (e.symm (z.1, t))) ρ z.2 - f.val (e.symm z)| ∂ν.prod volume := by
  have h := (MeasurePreserving.symm e he).lintegral_comp_emb e.symm.measurableEmbedding
    (fun x => ENNReal.ofReal |(averageInSplit e M hρ f).val x - f.val x|)
  simpa only [densityL1Distance, averageInSplit, precomposeBounded, averageLastCoordinate,
    MeasurableEquiv.apply_symm_apply] using h.symm

theorem coordinateAverage_polynomial_error {n : ℕ} {ι : Type*} [Fintype ι]
    (i : Fin (n + 1)) (M : ℝ) (D : ℕ) (hM : 0 ≤ M)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S)
    (p : (Fin n → ℝ) → ι → Polynomial ℝ)
    (hsupport : ∀ y ∉ S, ∀ t, f.val (i.insertNth t y) = 0)
    (hdepend : ∀ y ∈ S, ∀ t t',
      (∀ j, (p y j).eval t ≤ 0 ↔ (p y j).eval t' ≤ 0) →
        f.val (i.insertNth t y) = f.val (i.insertNth t' y))
    (hdegree : ∀ y ∈ S, ∑ j, (p y j).natDegree ≤ D)
    {ρ : ℝ} (hρ : 0 < ρ) :
    densityL1Distance volume (coordinateAverage i M hρ f).val f.val ≤
      ENNReal.ofReal (4 * M * (D : ℝ) * ρ) * volume S := by
  rw [coordinateAverage, averageInSplit_error_eq volume volume (coordinateSplit i)
    (coordinateSplit_measurePreserving i)]
  exact polynomial_cell_averaging_supported_product volume S hS p
    (fun y t => f.val (i.insertNth t y)) M D
    (f.property.1.comp (coordinateSplit i).symm.measurable) hM
    (fun y t => f.property.2 _) hsupport hdepend hdegree hρ

/-- A bounded nonnegative density whose coordinate fibers are polynomial
sign tables can be flattened into an actual rectangular mesh table.
Mass is preserved exactly and the error is bounded uniformly in every
polynomial coefficient. `V` bounds the volume of each transverse support. -/
theorem exists_flattened_density {n : ℕ} {ι : Type*} [Fintype ι]
    (M : ℝ) (D : ℕ) (hM : 0 ≤ M)
    (f : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M)
    (hf : ∀ x, 0 ≤ f.val x)
    (S : Fin (n + 1) → Set (Fin n → ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (p : Fin (n + 1) → (Fin n → ℝ) → ι → Polynomial ℝ)
    (hsupport : ∀ i y, y ∉ S i → ∀ t, f.val (i.insertNth t y) = 0)
    (hdepend : ∀ i y, y ∈ S i → ∀ t t',
      (∀ j, (p i y j).eval t ≤ 0 ↔ (p i y j).eval t' ≤ 0) →
        f.val (i.insertNth t y) = f.val (i.insertNth t' y))
    (hdegree : ∀ i y, y ∈ S i → ∑ j, (p i y j).natDegree ≤ D)
    (V : ℝ≥0∞) (hV : ∀ i, volume (S i) ≤ V)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : boundedMeasurableFunctions (Fin (n + 1) → ℝ) M,
      (∀ x, 0 ≤ g.val x) ∧
      (∫⁻ x, ENNReal.ofReal (g.val x)) = (∫⁻ x, ENNReal.ofReal (f.val x)) ∧
      (∀ x y, (∀ i, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → g.val x = g.val y) ∧
      densityL1Distance volume g.val f.val ≤
        ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (4 * M * (D : ℝ) * ρ) * V := by
  let L := List.finRange (n + 1)
  let g := L.foldr (fun i g => coordinateAverage i M hρ g) f
  refine ⟨g, coordinate_averaging_nonneg M hρ L f hf,
    coordinate_averaging_mass M hρ L f hf, ?_, ?_⟩
  · intro x y hfloor
    exact coordinate_averaging_same_cell M hρ L (fun i => List.mem_finRange i) f x y hfloor
  · have hE : ∀ i ∈ L,
        densityL1Distance volume (coordinateAverage i M hρ f).val f.val ≤
          ENNReal.ofReal (4 * M * (D : ℝ) * ρ) * V := by
      intro i _
      exact (coordinateAverage_polynomial_error i M D hM f (S i) (hS i) (p i)
        (hsupport i) (hdepend i) (hdegree i) hρ).trans
        (mul_le_mul_right (hV i) _)
    simpa only [L, List.length_finRange, mul_assoc] using
      coordinate_averaging_error_le M hρ L f
        (ENNReal.ofReal (4 * M * (D : ℝ) * ρ) * V) hE

end Submission.Lib.K4ModelReduction
