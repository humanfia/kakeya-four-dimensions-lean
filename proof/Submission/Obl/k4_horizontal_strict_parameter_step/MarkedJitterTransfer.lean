/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/MarkedJitterTransfer.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.MarkedJitter
import Submission.Obl.k4_horizontal_strict_parameter_step.GraphCellCaps

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- Finite marks preserve every original almost-everywhere test that is stable
throughout a physical mesh cell. The two graph evaluations use the same jitter. -/
theorem markedJitter_transport_ae {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (mark : Ω → ι) (hm : Measurable mark)
    (Z : Ω → Fin 3 → ℝ) (δ : ℝ) (F : Finset (Fin 3 → ℤ))
    {Q : Ω → Prop} {P : ι × (Fin 3 → ℝ) → Prop} (hQ : ∀ᵐ p ∂μ, Q p)
    (htransport : ∀ p, Q p → ∀ z, baseMesh δ z = baseMesh δ (Z p) → P (mark p, z)) :
    ∀ᵐ p ∂indexedBaseLaw (fun i => meshJitter δ F
      (fun q => (μ.restrict {p | mark p = i}) {p | baseMesh δ (Z p) = q})), P p := by
  apply indexedBaseLaw_ae
  intro i
  apply meshJitter_transport_ae (μ.restrict {p | mark p = i}) Z δ F
    (Q := fun p => Q p ∧ mark p = i)
  · filter_upwards [ae_restrict_of_ae hQ,
      ae_restrict_mem (measurableSet_eq_fun hm measurable_const)] with p hp hi
    exact ⟨hp, hi⟩
  · intro p hp z hz
    simpa only [hp.2] using htransport p hp.1 z hz

/-- Testing an event after jitter is charged to its original pre-jitter event.
This is the return map for band caps with pair-dependent source graph values. -/
theorem markedJitter_event_bound {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (mark : Ω → ι) (hm : Measurable mark)
    (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ)
    (F : Finset (Fin 3 → ℤ)) (A : Set Ω) (hA : MeasurableSet A)
    (B : ι → Set (Fin 3 → ℝ)) (hB : ∀ i, MeasurableSet (B i))
    (htransport : ∀ᵐ p ∂μ, ∀ z, baseMesh δ z = baseMesh δ (Z p) →
      z ∈ B (mark p) → p ∈ A) :
    indexedBaseLaw (fun i => meshJitter δ F
      (fun q => (μ.restrict {p | mark p = i}) {p | baseMesh δ (Z p) = q}))
      {p | p.2 ∈ B p.1} ≤ μ A := by
  rw [indexedBaseLaw_apply]
  change (∑ i, meshJitter δ F
    (fun q => (μ.restrict {p | mark p = i}) {p | baseMesh δ (Z p) = q}) (B i)) ≤ _
  calc
    _ ≤ ∑ i, (μ.restrict {p | mark p = i}) A := by
      apply Finset.sum_le_sum
      intro i _
      apply meshJitter_event_bound (μ.restrict {p | mark p = i}) Z hZ hδ F A hA (B i) (hB i)
      filter_upwards [ae_restrict_of_ae htransport,
        ae_restrict_mem (measurableSet_eq_fun hm measurable_const)] with p hp hi z hz hzB
      apply hp z hz
      simpa only [hi] using hzB
    _ = μ A := by
      simpa using marked_original_event_mass μ mark hm (fun _ => True) A hA

/-- A finite original pair law remains finite after cell redistribution.
Its mass is still expressed in the original incidence units. -/
theorem markedJitter_finite {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (mark : Ω → ι) (hm : Measurable mark)
    (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ)
    (F : Finset (Fin 3 → ℤ)) (hcover : ∀ᵐ p ∂μ, baseMesh δ (Z p) ∈ F) :
    IsFiniteMeasure (indexedBaseLaw (fun i => meshJitter δ F
      (fun q => (μ.restrict {p | mark p = i}) {p | baseMesh δ (Z p) = q}))) := by
  have hm := markedJitter_original_mass μ mark hm Z hZ hδ F hcover (fun _ => True)
  simp only [Set.ofPred_true] at hm
  constructor
  rw [hm]
  exact measure_lt_top μ univ

end

end Submission.Obl.k4_horizontal_strict_parameter_step
