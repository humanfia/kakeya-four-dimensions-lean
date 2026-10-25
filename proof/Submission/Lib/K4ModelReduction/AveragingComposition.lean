import Submission.Lib.K4ModelReduction.BaseCellMass

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Combining coordinate redistribution errors by L1 contraction. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory
open scoped ENNReal

noncomputable def densityL1Distance {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f g : Y → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal |f y - g y| ∂μ

theorem densityL1Distance_triangle {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f g h : Y → ℝ) (hf : Measurable f) (hg : Measurable g) :
    densityL1Distance μ f h ≤ densityL1Distance μ f g + densityL1Distance μ g h := by
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal |f y - g y| + ENNReal.ofReal |g y - h y| ∂μ := by
      apply lintegral_mono
      intro y
      exact (ENNReal.ofReal_le_ofReal (abs_sub_le (f y) (g y) (h y))).trans_eq
        (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _))
    _ = _ := lintegral_add_left (ENNReal.measurable_ofReal.comp (hf.sub hg).abs) _

def boundedMeasurableFunctions (Y : Type*) [MeasurableSpace Y] (M : ℝ) :=
  {f : Y → ℝ // Measurable f ∧ ∀ y, |f y| ≤ M}

/-- A finite sequence of contractions costs at most the sum of their
individual errors on the original density. No commutation or persistence
of a polynomial sign-table representation is needed. -/
theorem averaging_composition_error {Y ι : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (M : ℝ)
    (A : ι → boundedMeasurableFunctions Y M → boundedMeasurableFunctions Y M)
    (hcontract : ∀ i f g, densityL1Distance μ (A i f).val (A i g).val ≤
      densityL1Distance μ f.val g.val)
    (L : List ι) (f : boundedMeasurableFunctions Y M) :
    densityL1Distance μ (L.foldr (fun i g => A i g) f).val f.val ≤
      (L.map (fun i => densityL1Distance μ (A i f).val f.val)).sum := by
  induction L with
  | nil => simp [densityL1Distance]
  | cons i L ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    calc
      _ ≤ densityL1Distance μ (A i (L.foldr (fun j g => A j g) f)).val (A i f).val +
          densityL1Distance μ (A i f).val f.val :=
        densityL1Distance_triangle μ _ _ _
          (A i (L.foldr (fun j g => A j g) f)).property.1 (A i f).property.1
      _ ≤ densityL1Distance μ (L.foldr (fun j g => A j g) f).val f.val +
          densityL1Distance μ (A i f).val f.val :=
        add_le_add (hcontract i (L.foldr (fun j g => A j g) f) f) le_rfl
      _ ≤ (L.map (fun j => densityL1Distance μ (A j f).val f.val)).sum +
          densityL1Distance μ (A i f).val f.val := add_le_add ih le_rfl
      _ = _ := add_comm _ _

noncomputable def averageLastCoordinate {Y : Type*} [MeasurableSpace Y]
    (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (f : boundedMeasurableFunctions (Y × ℝ) M) : boundedMeasurableFunctions (Y × ℝ) M :=
  ⟨fun z => meshAverage (fun x => f.val (z.1, x)) ρ z.2,
    meshAverage_measurable (fun y x => f.val (y, x)) f.property.1 hρ,
    fun z => meshAverage_abs_le _ hρ (fun x => f.property.2 (z.1, x)) z.2⟩

theorem averageLastCoordinate_contract {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (f g : boundedMeasurableFunctions (Y × ℝ) M) :
    densityL1Distance (μ.prod volume) (averageLastCoordinate M hρ f).val
      (averageLastCoordinate M hρ g).val ≤ densityL1Distance (μ.prod volume) f.val g.val :=
  meshAverage_product_abs_sub_le μ (fun y x => f.val (y, x)) (fun y x => g.val (y, x))
    f.property.1 g.property.1 M M (fun y x => f.property.2 (y, x))
    (fun y x => g.property.2 (y, x)) hρ

def precomposeBounded {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (φ : X → Y) (hφ : Measurable φ) (M : ℝ)
    (f : boundedMeasurableFunctions Y M) : boundedMeasurableFunctions X M :=
  ⟨fun x => f.val (φ x), f.property.1.comp hφ, fun x => f.property.2 (φ x)⟩

theorem densityL1Distance_precompose {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (φ : X → Y)
    (hφ : MeasurePreserving φ μ ν) (M : ℝ) (f g : boundedMeasurableFunctions Y M) :
    densityL1Distance μ (precomposeBounded φ hφ.measurable M f).val
      (precomposeBounded φ hφ.measurable M g).val = densityL1Distance ν f.val g.val :=
  hφ.lintegral_comp (ENNReal.measurable_ofReal.comp (f.property.1.sub g.property.1).abs)

/-- Average in the scalar coordinate of a measure-preserving coordinate split. -/
noncomputable def averageInSplit {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y × ℝ) (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (f : boundedMeasurableFunctions X M) : boundedMeasurableFunctions X M :=
  precomposeBounded e e.measurable M
    (averageLastCoordinate M hρ (precomposeBounded e.symm e.symm.measurable M f))

theorem averageInSplit_contract {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y × ℝ)
    (he : MeasurePreserving e μ (ν.prod volume)) (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (f g : boundedMeasurableFunctions X M) :
    densityL1Distance μ (averageInSplit e M hρ f).val (averageInSplit e M hρ g).val ≤
      densityL1Distance μ f.val g.val := by
  let f' := precomposeBounded e.symm e.symm.measurable M f
  let g' := precomposeBounded e.symm e.symm.measurable M g
  calc
    _ = densityL1Distance (ν.prod volume) (averageLastCoordinate M hρ f').val
        (averageLastCoordinate M hρ g').val :=
      densityL1Distance_precompose μ (ν.prod volume) e he M _ _
    _ ≤ densityL1Distance (ν.prod volume) f'.val g'.val :=
      averageLastCoordinate_contract ν M hρ f' g'
    _ = _ := densityL1Distance_precompose (ν.prod volume) μ e.symm
      (MeasurePreserving.symm e he) M f g

theorem averageInSplit_nonneg {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y × ℝ) (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (f : boundedMeasurableFunctions X M) (hf : ∀ x, 0 ≤ f.val x) :
    ∀ x, 0 ≤ (averageInSplit e M hρ f).val x := by
  intro x
  exact integral_nonneg fun t => hf (e.symm ((e x).1, t))

theorem averageInSplit_mass {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (e : X ≃ᵐ Y × ℝ)
    (he : MeasurePreserving e μ (ν.prod volume)) (M : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (f : boundedMeasurableFunctions X M) (hf : ∀ x, 0 ≤ f.val x) :
    (∫⁻ x, ENNReal.ofReal ((averageInSplit e M hρ f).val x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (f.val x) ∂μ := by
  let f' := precomposeBounded e.symm e.symm.measurable M f
  calc
    _ = ∫⁻ z, ENNReal.ofReal ((averageLastCoordinate M hρ f').val z) ∂ν.prod volume :=
      he.lintegral_comp (ENNReal.measurable_ofReal.comp (averageLastCoordinate M hρ f').property.1)
    _ = ∫⁻ z, ENNReal.ofReal (f'.val z) ∂ν.prod volume :=
      meshAverage_product_mass ν (fun y t => f'.val (y, t)) f'.property.1 M
        (fun y t => f'.property.2 (y, t)) (fun y t => hf (e.symm (y, t))) hρ
    _ = _ := (MeasurePreserving.symm e he).lintegral_comp
      (ENNReal.measurable_ofReal.comp f.property.1)

end Submission.Lib.K4ModelReduction
