-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.WholeStateFloors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/WholeStateFloors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/WholeStateFloors.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/WholeStateFloors.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_scalar_grid_parameter_preparation.WeightedPartitionFloors
import Submission.Obl.k4_scalar_heavy_intercept_selection.PositiveCodes


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- A union of whole fine states leaves every surviving fine-state
conditional law exactly equal to its ORIGINAL law. -/
theorem restrict_whole_state_fiber {Ω Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] (μ : Measure Ω) (state : Ω → Q) (hm : Measurable state)
    (U : Set Q) (q : Q) (hq : q ∈ U) :
    (μ.restrict (state ⁻¹' U)).restrict (state ⁻¹' {q}) = μ.restrict (state ⁻¹' {q}) := by
  rw [Measure.restrict_restrict (hm (measurableSet_singleton q))]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, h ▸ hq⟩

/-- Run the ACCEPTED simultaneous weighted pruning on the ORIGINAL
fine-state law, then pull it back. Thus all final group floors hold
at once, every retained original fine fiber has positive mass, and
all selections are literal unions of whole original fine states. -/
theorem simultaneous_whole_state_floors {Ω Q I C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [Countable Q] [Fintype I] [DecidableEq C] (μ : Measure Ω) [IsFiniteMeasure μ]
    (state : Ω → Q) (hm : Measurable state) (F : Finset Q)
    (hcarrier : ∀ᵐ x ∂μ, state x ∈ F) (code : I → Q → C) (w : I → C → ENNReal) :
    ∃ U : Set Q, MeasurableSet U ∧ U ⊆ (F : Set Q) ∧
      μ univ ≤ μ (state ⁻¹' U) + ∑ i : I, ∑ c ∈ F.image (code i), w i c ∧
      (∀ i x, state x ∈ U → w i (code i (state x)) ≤
        (μ.restrict (state ⁻¹' U)) {y | code i (state y) = code i (state x)}) ∧
      ∀ x, state x ∈ U →
        (μ.restrict (state ⁻¹' U)) (state ⁻¹' {state x}) ≠ 0 := by
  classical
  let P := Submission.Obl.k4_scalar_heavy_intercept_selection.positiveCodeWindow μ state F
  have hPsub : P ⊆ F := Finset.filter_subset _ _
  have hPae : ∀ᵐ x ∂μ, state x ∈ P :=
    Submission.Obl.k4_scalar_heavy_intercept_selection.ae_mem_positiveCodeWindow
      μ μ le_rfl state hm F hcarrier
  have hPfull : (μ.map state) (P : Set Q) = μ univ := by
    rw [Measure.map_apply hm P.measurableSet]
    apply measure_congr
    filter_upwards [hPae] with x hx
    simp only [mem_preimage, Finset.mem_coe, hx, mem_univ]
  let codeFinite (i : I) := P.finite_toSet.image (code i)
  obtain ⟨U,hU,hUP,hloss,hfloor⟩ :=
    Submission.Obl.k4_scalar_grid_parameter_preparation.simultaneous_weighted_partition_floors
      (μ.map state) (P : Set Q) P.measurableSet (by finiteness) code
      (fun i c => (Set.to_countable {q | code i q = c}).measurableSet) codeFinite w
  have hUF : U ⊆ (F : Set Q) := fun q hq => hPsub (hUP hq)
  have hsum : (∑ i : I, ∑ c ∈ (codeFinite i).toFinset, w i c) ≤
      ∑ i : I, ∑ c ∈ F.image (code i), w i c := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum_of_subset
    intro c hc
    obtain ⟨q,hq,hqc⟩ := (codeFinite i).mem_toFinset.mp hc
    exact Finset.mem_image.mpr ⟨q,hPsub hq,hqc⟩
  refine ⟨U,hU,hUF,?_,?_,?_⟩
  · calc
      μ univ = (μ.map state) (P : Set Q) := hPfull.symm
      _ ≤ (μ.map state) (U ∪ ((P : Set Q) \ U)) := measure_mono (by
        intro q hq
        by_cases h : q ∈ U
        · exact Or.inl h
        · exact Or.inr ⟨hq,h⟩)
      _ ≤ (μ.map state) U + (μ.map state) ((P : Set Q) \ U) := measure_union_le _ _
      _ ≤ (μ.map state) U + ∑ i : I, ∑ c ∈ F.image (code i), w i c :=
        add_le_add le_rfl (hloss.trans hsum)
      _ = _ := by rw [Measure.map_apply hm hU]
  · intro i x hx
    have hs : MeasurableSet {q | code i q = code i (state x)} :=
      (Set.to_countable _).measurableSet
    have hf := hfloor i (state x) hx
    have hmap := Measure.restrict_map (μ := μ) hm hU
    have heq : (μ.map state) (U ∩ {q | code i q = code i (state x)}) =
        (μ.restrict (state ⁻¹' U)) {y | code i (state y) = code i (state x)} := by
      rw [inter_comm U, ← Measure.restrict_apply hs, hmap, Measure.map_apply hm hs]
      rfl
    exact heq ▸ hf
  · intro x hx
    have hp := (Finset.mem_filter.mp (hUP hx)).2
    have heq := restrict_whole_state_fiber μ state hm U (state x) hx
    have hh := congrArg (fun ν : Measure Ω => ν univ) heq
    simp only [Measure.restrict_apply_univ] at hh
    rw [hh]
    exact hp

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
