-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.StripPruning, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/StripPruning.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenStripPruning.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenStripPruning.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.FiniteStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WholeStateFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.PacketStripBudgets


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- Simultaneously restore all ORIGINAL strip-prior floors on one
final union of whole fine physical states. The original supporting
priors are fixed before this selection; they are never recomputed from
successful incidence mass. Every retained strip has positive final mass. -/
theorem select_original_strip_family {I : Type*} [Fintype I]
    (p : PhysicalModel) (ν : Measure Ln) (hκ : 1 ≤ p.slack)
    (μ : Measure Ev) [IsFiniteMeasure μ]
    {E : Set Ev} (hEp : E ⊆ p.event) (hfull : ∀ᵐ z ∂μ, z ∈ E)
    (b ρ : ℝ) (hb : 0 < b) (width : I → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (a J : I → ENNReal)
    (hbudget : ∀ i, ∀ F : Finset ((Fin 4 → ℤ) × ℤ),
      (∑ c ∈ F, (p.prior ν) (p.stripSupport E b ρ (width i) row c)) ≤
        J i * (p.prior ν) univ) :
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      μ univ ≤ μ ((p.physicalState b) ⁻¹' U) +
        ∑ i : I, a i * J i * (p.prior ν) univ ∧
      (∀ i z, p.physicalState b z ∈ U →
        a i * (p.prior ν) (p.stripSupport E b ρ (width i) row
          (p.stripLabel b ρ (width i) row z)) ≤
        (μ.restrict ((p.physicalState b) ⁻¹' U))
          ((p.stripLabel b ρ (width i) row) ⁻¹' {p.stripLabel b ρ (width i) row z})) ∧
      ∀ i z, p.physicalState b z ∈ U →
        (μ.restrict ((p.physicalState b) ⁻¹' U))
          ((p.stripLabel b ρ (width i) row) ⁻¹' {p.stripLabel b ρ (width i) row z}) ≠ 0 := by
  classical
  obtain ⟨F,hF⟩ := p.exists_original_fine_state_carrier hκ hEp hb
  have hcarrier : ∀ᵐ z ∂μ, p.physicalState b z ∈ F := hfull.mono fun z hz => hF z hz
  let code : I → (Fin 4 → ℤ) → ((Fin 4 → ℤ) × ℤ) := fun i =>
    nativeStripState b ρ (width i) row
  let w : I → ((Fin 4 → ℤ) × ℤ) → ENNReal := fun i c =>
    a i * (p.prior ν) (p.stripSupport E b ρ (width i) row c)
  obtain ⟨U,hU,_,hloss,hfloor,hpositive⟩ := simultaneous_whole_state_floors
    μ (p.physicalState b) (p.measurable_physicalState b) F hcarrier code w
  have hsum : (∑ i : I, ∑ c ∈ F.image (code i), w i c) ≤
      ∑ i : I, a i * J i * (p.prior ν) univ := by
    apply Finset.sum_le_sum
    intro i _
    dsimp only [w]
    rw [← Finset.mul_sum, mul_assoc]
    exact mul_le_mul' le_rfl (hbudget i _)
  refine ⟨U,hU,hloss.trans (add_le_add le_rfl hsum),?_,?_⟩
  · intro i z hz
    have hf := hfloor i z hz
    simpa only [w, code, ← p.stripLabel_eq_state, Set.preimage, Set.mem_singleton_iff] using hf
  · intro i z hz
    have hp := hpositive z hz
    have hsub : (p.physicalState b) ⁻¹' {p.physicalState b z} ⊆
        (p.stripLabel b ρ (width i) row) ⁻¹' {p.stripLabel b ρ (width i) row z} := by
      intro z' hz'
      change p.physicalState b z' = p.physicalState b z at hz'
      change p.stripLabel b ρ (width i) row z' = p.stripLabel b ρ (width i) row z
      rw [p.stripLabel_eq_state, p.stripLabel_eq_state, hz']
    exact ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hp) (measure_mono hsub))

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
