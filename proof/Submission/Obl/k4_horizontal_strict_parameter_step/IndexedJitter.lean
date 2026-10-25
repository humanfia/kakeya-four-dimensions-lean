/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/IndexedJitter.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.MeshJitter

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Keep the original finite pair label when redistributing its base mass. -/
def indexedBaseLaw {ι X : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSpace X]
    (μ : ι → Measure X) : Measure (ι × X) :=
  ∑ i, (μ i).map (fun z => (i, z))

theorem indexedBaseLaw_apply {ι X : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace X] (μ : ι → Measure X)
    (B : Set (ι × X)) :
    indexedBaseLaw μ B = ∑ i, μ i ((fun z => (i, z)) ⁻¹' B) := by
  simp only [indexedBaseLaw, Measure.finsetSum_apply,
    (measurableEmbedding_prodMk_left _).map_apply]

theorem indexedBaseLaw_ae {ι X : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace X] (μ : ι → Measure X)
    {P : ι × X → Prop} (hP : ∀ i, ∀ᵐ z ∂μ i, P (i, z)) :
    ∀ᵐ p ∂indexedBaseLaw μ, P p := by
  unfold indexedBaseLaw
  rw [ae_finsetSum_measure_iff]
  intro i hi
  exact (measurableEmbedding_prodMk_left i).ae_map_iff.mpr (hP i)

theorem indexedBaseLaw_label {ι X : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace X] (μ : ι → Measure X)
    (P : ι → Prop) :
    indexedBaseLaw μ {p | P p.1} = ∑ i, if P i then μ i univ else 0 := by
  classical
  rw [indexedBaseLaw_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : P i <;> simp [h]

/-- A marginal density estimate can be checked before installing the finite marks.
The coordinate map may depend on the common colour of the pair. -/
theorem indexedBaseLaw_marginal {ι J X Y : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : ι → Measure X) (mark : ι → J) (Z : ι → X → Y)
    (ν : Measure Y) (C : J → ENNReal)
    (hcap : ∀ j (U : Set Y), MeasurableSet U →
      (∑ i, if mark i = j then μ i (Z i ⁻¹' U) else 0) ≤ C j * ν U)
    (j : J) (U : Set Y) (hU : MeasurableSet U) :
    indexedBaseLaw μ {p | mark p.1 = j ∧ Z p.1 p.2 ∈ U} ≤ C j * ν U := by
  classical
  rw [indexedBaseLaw_apply]
  convert hcap j U hU using 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : mark i = j
  · rw [ite_eq_left h]
    congr 1
    ext z
    simp [h]
  · simp [h]

/-- Badness depending only on the stored pair is charged in exactly the original
incidence units, even after simultaneous jitter of its two graph evaluations. -/
theorem indexedJitter_label_mass {ι Ω : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace Ω]
    (μ : ι → Measure Ω) (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (F : Finset (Fin 3 → ℤ))
    (hcover : ∀ i, ∀ᵐ p ∂μ i, baseMesh δ (Z p) ∈ F) (P : ι → Prop) :
    indexedBaseLaw (fun i => meshJitter δ F (fun q => μ i {p | baseMesh δ (Z p) = q}))
        {p | P p.1} = ∑ i, if P i then μ i univ else 0 := by
  rw [indexedBaseLaw_label]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · exact meshJitter_original_mass (μ i) hZ hδ F (hcover i)
  · rfl

/-- A colour sum of original cell caps supplies the continuous marked marginal.
No source, witness, or paired-entry count appears in the ceiling. -/
theorem indexedJitter_marginal {ι J : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (mark : ι → J) {δ : ℝ} (hδ : 0 < δ)
    (F : Finset (Fin 3 → ℤ)) (w : ι → (Fin 3 → ℤ) → ENNReal) (C : J → ENNReal)
    (hcap : ∀ j q, q ∈ F →
      (∑ i, if mark i = j then w i q else 0) ≤ C j * ENNReal.ofReal (δ ^ 3))
    (j : J) (U : Set (Fin 3 → ℝ)) (hU : MeasurableSet U) :
    indexedBaseLaw (fun i => meshJitter δ F (w i))
      {p | mark p.1 = j ∧ p.2 ∈ U} ≤ C j * volume U := by
  classical
  apply indexedBaseLaw_marginal (fun i => meshJitter δ F (w i)) mark
    (fun _ z => z) volume C ?_ j U hU
  intro j U hU
  let I : Finset ι := Finset.univ.filter (fun i => mark i = j)
  have hsum := sum_meshJitter_le_volume hδ F I w (C j) (by
    intro q hq
    simpa [I, Finset.sum_filter] using hcap j q hq)
  have hb := hsum U
  rw [Measure.finsetSum_apply, Measure.smul_apply] at hb
  change (∑ i ∈ I, meshJitter δ F (w i) U) ≤ C j * volume U at hb
  dsimp only [I] at hb
  rw [Finset.sum_filter] at hb
  change (∑ i, if mark i = j then meshJitter δ F (w i) U else 0) ≤ C j * volume U
  exact hb

end

end Submission.Obl.k4_horizontal_strict_parameter_step
