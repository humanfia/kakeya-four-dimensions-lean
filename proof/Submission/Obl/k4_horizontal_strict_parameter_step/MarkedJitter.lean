/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/MarkedJitter.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.IndexedJitter

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Reassembling finite marks preserves the original event measure exactly. -/
theorem marked_original_event_mass {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (mark : Ω → ι) (hm : Measurable mark) (P : ι → Prop)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∑ i, if P i then (μ.restrict {p | mark p = i}) A else 0) =
      μ (A ∩ {p | P (mark p)}) := by
  rw [← Finset.sum_filter]
  let I := Finset.univ.filter P
  change (∑ i ∈ I, (μ.restrict {p | mark p = i}) A) = _
  simp_rw [Measure.restrict_apply hA]
  have hsets (i : ι) : MeasurableSet (A ∩ {p | mark p = i}) :=
    hA.inter (measurableSet_eq_fun hm measurable_const)
  have hd : (↑I : Set ι).PairwiseDisjoint (fun i => A ∩ {p | mark p = i}) := by
    intro i hi i' hi' hne
    apply disjoint_left.mpr
    rintro p ⟨_, hp⟩ ⟨_, hp'⟩
    exact hne (hp.symm.trans hp')
  rw [← measure_biUnion_finset hd (fun i _ => hsets i)]
  congr 1
  ext p
  simp only [mem_iUnion, exists_prop, mem_inter_iff, mem_setOf_eq, I,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hpA, hpi⟩
    exact ⟨hpA, hpi.symm ▸ hi⟩
  · rintro ⟨hpA, hp⟩
    exact ⟨mark p, hp, hpA, rfl⟩

/-- All pair-dependent discrepancy events return in original incidence units.
The finite marks may contain both the old predictor and the true affine entry. -/
theorem markedJitter_original_mass {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (mark : Ω → ι) (hm : Measurable mark)
    (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ)
    (F : Finset (Fin 3 → ℤ)) (hcover : ∀ᵐ p ∂μ, baseMesh δ (Z p) ∈ F) (P : ι → Prop) :
    indexedBaseLaw (fun i => meshJitter δ F
      (fun q => (μ.restrict {p | mark p = i}) {p | baseMesh δ (Z p) = q})) {p | P p.1} =
        μ {p | P (mark p)} := by
  rw [indexedJitter_label_mass (fun i => μ.restrict {p | mark p = i}) Z hZ hδ F
    (fun i => ae_restrict_of_ae hcover) P,
    marked_original_event_mass μ mark hm P univ MeasurableSet.univ, univ_inter]

/-- A cap on an original colour event becomes the continuous marked marginal,
with every pair label retained and no factor for the number of marked entries. -/
theorem markedJitter_marginal {Ω ι J : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) (mark : Ω → ι) (hm : Measurable mark) (colour : ι → J)
    (Z : Ω → Fin 3 → ℝ) (hZ : Measurable Z) {δ : ℝ} (hδ : 0 < δ)
    (F : Finset (Fin 3 → ℤ)) (C : J → ENNReal)
    (hcap : ∀ j q, q ∈ F → μ {p | baseMesh δ (Z p) = q ∧ colour (mark p) = j} ≤
      C j * ENNReal.ofReal (δ ^ 3))
    (j : J) (U : Set (Fin 3 → ℝ)) (hU : MeasurableSet U) :
    indexedBaseLaw (fun i => meshJitter δ F
      (fun q => (μ.restrict {p | mark p = i}) {p | baseMesh δ (Z p) = q}))
      {p | colour p.1 = j ∧ p.2 ∈ U} ≤ C j * volume U := by
  apply indexedJitter_marginal colour hδ F _ C ?_ j U hU
  intro j q hq
  rw [marked_original_event_mass μ mark hm (fun i => colour i = j)
    {p | baseMesh δ (Z p) = q} ((measurable_baseMesh δ).comp hZ (measurableSet_singleton q))]
  exact hcap j q hq

end

end Submission.Obl.k4_horizontal_strict_parameter_step
