-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalWorldSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalWorldSelection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalWorldSelection.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalWorldSelection.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Mathlib
import Submission.Lib.K4FinalLawSelection
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.UnitIncidenceKernel
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.Conditioning


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Choose an original parameter world by its FULL prior mass. The
number of possible worlds, including countably many null worlds, costs
no factor. No incidence mass is used as a new prior denominator. -/
theorem exists_original_world_mass {X T J : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace J]
    [MeasurableSingletonClass J] [Countable J]
    (ν : Measure X) [IsProbabilityMeasure ν] (τ : Measure T) [IsProbabilityMeasure τ]
    (bin : X → J) (hbin : Measurable bin) (E : Set (X × T))
    (δ : ℝ) (hδ : 0 < δ) (hmass : ENNReal.ofReal δ ≤ (ν.prod τ) E) :
    ∃ j : J, ν (bin ⁻¹' {j}) ≠ 0 ∧
      ENNReal.ofReal (δ / 2) * ν (bin ⁻¹' {j}) ≤
        (ν.prod τ) (E ∩ ((bin ⁻¹' {j}) ×ˢ univ)) := by
  classical
  have hmeas (j : J) : MeasurableSet (bin ⁻¹' {j}) := hbin (measurableSet_singleton j)
  have hdisjoint : Pairwise (fun i j : J => Disjoint (bin ⁻¹' {i}) (bin ⁻¹' {j})) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    exact hij (hx.symm.trans hy)
  have huniv : (⋃ j : J, bin ⁻¹' {j}) = univ := by ext x; simp
  have hweights : (∑' j : J, ν (bin ⁻¹' {j})) ≤ 1 := by
    have h := tsum_meas_le_meas_iUnion_of_disjoint ν hmeas hdisjoint
    simpa only [huniv, measure_univ] using h
  have hcover : (⋃ j : J, E ∩ ((bin ⁻¹' {j}) ×ˢ (univ : Set T))) = E := by
    ext z
    simp only [mem_iUnion, mem_inter_iff, mem_prod, mem_preimage, mem_singleton_iff,
      mem_univ, and_true]
    constructor
    · rintro ⟨_, hz, _⟩; exact hz
    · intro hz; exact ⟨bin z.1, hz, rfl⟩
  by_contra hnone
  have hcap (j : J) : (ν.prod τ) (E ∩ ((bin ⁻¹' {j}) ×ˢ univ)) ≤
      ENNReal.ofReal (δ / 2) * ν (bin ⁻¹' {j}) := by
    by_cases hj : ν (bin ⁻¹' {j}) = 0
    · have hnull : (ν.prod τ) ((bin ⁻¹' {j}) ×ˢ univ) = 0 := by
        rw [Measure.prod_prod, hj, zero_mul]
      rw [hj, mul_zero]
      exact le_of_eq (measure_mono_null inter_subset_right hnull)
    · exact (lt_of_not_ge (fun h => hnone ⟨j, hj, h⟩)).le
  have hsmall : (ν.prod τ) E ≤ ENNReal.ofReal (δ / 2) := by
    calc
      _ = (ν.prod τ) (⋃ j : J, E ∩ ((bin ⁻¹' {j}) ×ˢ univ)) := by rw [hcover]
      _ ≤ ∑' j : J, (ν.prod τ) (E ∩ ((bin ⁻¹' {j}) ×ˢ univ)) := measure_iUnion_le _
      _ ≤ ∑' j : J, ENNReal.ofReal (δ / 2) * ν (bin ⁻¹' {j}) := ENNReal.tsum_le_tsum hcap
      _ = ENNReal.ofReal (δ / 2) * ∑' j : J, ν (bin ⁻¹' {j}) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (δ / 2) * 1 := mul_le_mul' le_rfl hweights
      _ = _ := mul_one _
  have hstrict : ENNReal.ofReal (δ / 2) < ENNReal.ofReal δ :=
    (ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by linarith)
  exact (not_le_of_gt hstrict) (hmass.trans hsmall)

/-- The selected world's actual original conditional prior is a
probability and its retained labels have dense product-prior mass. -/
theorem exists_original_parameter_world {X T J : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace J]
    [MeasurableSingletonClass J] [Countable J]
    (ν : Measure X) [IsProbabilityMeasure ν] (τ : Measure T) [IsProbabilityMeasure τ]
    (bin : X → J) (hbin : Measurable bin) {E : Set (X × T)} (hE : MeasurableSet E)
    (δ : ℝ) (hδ : 0 < δ) (hmass : ENNReal.ofReal δ ≤ (ν.prod τ) E) :
    ∃ j : J, ν (bin ⁻¹' {j}) ≠ 0 ∧
      IsProbabilityMeasure ((ν (bin ⁻¹' {j}))⁻¹ • ν.restrict (bin ⁻¹' {j})) ∧
      ENNReal.ofReal (δ / 2) ≤
        (((ν (bin ⁻¹' {j}))⁻¹ • ν.restrict (bin ⁻¹' {j})).prod τ)
          (E ∩ ((bin ⁻¹' {j}) ×ˢ univ)) := by
  obtain ⟨j, hj, hmassj⟩ := exists_original_world_mass ν τ bin hbin E δ hδ hmass
  let A := bin ⁻¹' {j}
  have hA : MeasurableSet A := hbin (measurableSet_singleton j)
  have hprob := Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior_probability
    ν A (MeasurableEquiv.refl X) hj (measure_ne_top _ _)
  have hprob' : IsProbabilityMeasure ((ν A)⁻¹ • ν.restrict A) := by
    change IsProbabilityMeasure ((ν A)⁻¹ • Measure.map id (ν.restrict A)) at hprob
    simpa only [Measure.map_id] using hprob
  refine ⟨j, hj, hprob', ?_⟩
  change ENNReal.ofReal (δ / 2) ≤ (((ν A)⁻¹ • ν.restrict A).prod τ) (E ∩ (A ×ˢ univ))
  rw [Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_prod_eq_prod_univ A, Measure.restrict_apply (hE.inter (hA.prod MeasurableSet.univ)),
    inter_eq_left.mpr inter_subset_right]
  have h := mul_le_mul' (le_refl (ν A)⁻¹) hmassj
  have heq : (ν A)⁻¹ * (ENNReal.ofReal (δ / 2) * ν A) = ENNReal.ofReal (δ / 2) := by
    rw [mul_comm (ENNReal.ofReal (δ / 2)), ← mul_assoc,
      ENNReal.inv_mul_cancel hj (measure_ne_top _ _), one_mul]
  exact heq.symm.trans_le h

/-- An original reference submeasure supplies dense product-prior
labels by domination. Only the original event and original product law
occur in this comparison. -/
theorem original_product_mass_of_domination {Ω : Type*} [MeasurableSpace Ω]
    (P reference : Measure Ω) {E : Set Ω} (hE : MeasurableSet E)
    (K m : ℝ) (hK : 0 < K) (hdom : reference ≤ ENNReal.ofReal K • P)
    (hfull : reference Eᶜ = 0) (hmass : ENNReal.ofReal m ≤ reference univ) :
    ENNReal.ofReal (m / K) ≤ P E := by
  have hreference : reference univ = reference E := by
    simpa only [hfull, add_zero] using (measure_add_measure_compl (μ := reference) hE).symm
  have hcap : ENNReal.ofReal m ≤ ENNReal.ofReal K * P E := by
    rw [hreference] at hmass
    exact hmass.trans (by simpa only [Measure.smul_apply, smul_eq_mul] using hdom E)
  rw [ENNReal.ofReal_div_of_pos hK, div_eq_mul_inv, mul_comm]
  calc
    _ ≤ (ENNReal.ofReal K)⁻¹ * (ENNReal.ofReal K * P E) := mul_le_mul' le_rfl hcap
    _ = P E := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hK).ne'
        ENNReal.ofReal_ne_top, one_mul]

/-- The parameter world is selected from an actual retained original
reference law. Its labels have dense mass under the ORIGINAL full-bin
conditional prior, rather than under a normalized successful law. -/
theorem exists_original_parameter_world_of_reference {X T J : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace J]
    [MeasurableSingletonClass J] [Countable J]
    (ν : Measure X) [IsProbabilityMeasure ν] (τ : Measure T) [IsProbabilityMeasure τ]
    (reference : Measure (X × T)) (bin : X → J) (hbin : Measurable bin)
    {E : Set (X × T)} (hE : MeasurableSet E)
    (K m : ℝ) (hK : 0 < K) (hm : 0 < m)
    (hdom : reference ≤ ENNReal.ofReal K • (ν.prod τ))
    (hfull : reference Eᶜ = 0) (hmass : ENNReal.ofReal m ≤ reference univ) :
    ∃ j : J, ν (bin ⁻¹' {j}) ≠ 0 ∧
      IsProbabilityMeasure ((ν (bin ⁻¹' {j}))⁻¹ • ν.restrict (bin ⁻¹' {j})) ∧
      ENNReal.ofReal (m / (2 * K)) ≤
        (((ν (bin ⁻¹' {j}))⁻¹ • ν.restrict (bin ⁻¹' {j})).prod τ)
          (E ∩ ((bin ⁻¹' {j}) ×ˢ univ)) := by
  have hproduct := original_product_mass_of_domination (ν.prod τ) reference hE K m hK hdom hfull hmass
  obtain ⟨j, hj, hprob, hlabels⟩ := exists_original_parameter_world ν τ bin hbin hE
    (m / K) (div_pos hm hK) hproduct
  refine ⟨j, hj, hprob, ?_⟩
  simpa only [div_div, mul_comm K (2 : ℝ)] using hlabels

/-- Choose a dense full ORIGINAL parameter world from an actual unit-time
reference submeasure. The result uses ordinary Lebesgue duration, with
the full original bin mass as prior denominator and no world-count loss. -/
theorem exists_original_parameter_world_of_unit_reference {X J : Type*}
    [MeasurableSpace X] [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    (ν : Measure X) [IsProbabilityMeasure ν] (reference : Measure (X × ℝ))
    (bin : X → J) (hbin : Measurable bin) {E : Set (X × ℝ)} (hE : MeasurableSet E)
    (hEU : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (K m : ℝ) (hK : 0 < K) (hm : 0 < m)
    (hdom : reference ≤ ENNReal.ofReal K • ν.prod volume)
    (hfull : reference Eᶜ=0) (hmass : ENNReal.ofReal m ≤ reference univ) :
    ∃ j : J, ν (bin ⁻¹' {j}) ≠ 0 ∧
      IsProbabilityMeasure ((ν (bin ⁻¹' {j}))⁻¹ • ν.restrict (bin ⁻¹' {j})) ∧
      ENNReal.ofReal (m/(2*K)) ≤
        (((ν (bin ⁻¹' {j}))⁻¹ • ν.restrict (bin ⁻¹' {j})).prod volume)
          (E ∩ ((bin ⁻¹' {j}) ×ˢ univ)) := by
  letI : IsProbabilityMeasure unitTimeReference := unitTimeReference_probability
  have hfullTime : reference (univ ×ˢ Icc (0 : ℝ) 1)ᶜ=0 :=
    measure_mono_null (compl_subset_compl.mpr hEU) hfull
  have hunit := Submission.Lib.K4FinalLawSelection.dominated_restrict_time ν volume reference
    (ENNReal.ofReal K) (Icc (0 : ℝ) 1) hdom hfullTime
  obtain ⟨j,hj,hprob,hdense⟩ := exists_original_parameter_world_of_reference ν unitTimeReference
    reference bin hbin hE K m hK hm hunit hfull hmass
  refine ⟨j,hj,hprob,hdense.trans ?_⟩
  letI := hprob
  have hprod := Measure.prod_mono
    (le_refl ((ν (bin ⁻¹' {j}))⁻¹ • ν.restrict (bin ⁻¹' {j})))
    (show unitTimeReference ≤ volume from Measure.restrict_le_self)
  exact hprod _

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
