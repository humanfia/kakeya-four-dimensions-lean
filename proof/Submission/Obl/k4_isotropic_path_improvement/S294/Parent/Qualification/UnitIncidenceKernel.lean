-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.UnitIncidenceKernel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/UnitIncidenceKernel.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/UnitIncidenceKernel.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/UnitIncidenceKernel.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Lib.K4ScalarActualSwitching.BoundedIncidence

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- The original unit time reference, before any duration deletion. -/
def unitTimeReference : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

theorem unitTimeReference_probability : IsProbabilityMeasure unitTimeReference := by
  constructor
  simp [unitTimeReference, Real.volume_Icc]

section Event

variable {X : Type*} [MeasurableSpace X]

def originalUnitEventDensity (E : Set (X × ℝ)) : X × ℝ → ENNReal :=
  E.indicator (fun _ => 1)

theorem originalUnitEventDensity_measurable {E : Set (X × ℝ)} (hE : MeasurableSet E) :
    Measurable (originalUnitEventDensity E) := measurable_const.indicator hE

theorem originalUnitEventDensity_le_one (E : Set (X × ℝ)) (z : X × ℝ) :
    originalUnitEventDensity E z ≤ 1 := by
  by_cases hz : z ∈ E <;> simp [originalUnitEventDensity, hz]

/-- The bounded-density construction is exactly the original incidence
restriction with Lebesgue time, since the event is in the unit block. -/
theorem unit_event_withDensity (ν : Measure X) [SFinite ν]
    {E : Set (X × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (ν.prod unitTimeReference).withDensity (originalUnitEventDensity E) =
      (ν.prod volume).restrict E := by
  rw [originalUnitEventDensity, withDensity_indicator hE, withDensity_const, one_smul]
  have hprod : ν.prod unitTimeReference =
      (ν.prod volume).restrict (univ ×ˢ Icc (0 : ℝ) 1) := by
    simpa only [Measure.restrict_univ, unitTimeReference] using
      (Measure.prod_restrict (μ := ν) (ν := volume) univ (Icc (0 : ℝ) 1))
  rw [hprod, Measure.restrict_restrict_of_subset hunit]

/-- Construct the genuine conditional time kernel of the original event.
The original prior pays for short lines; surviving mass is never used
as a new denominator. The conditional-kernel theorem is imported. -/
theorem original_unit_event_time_kernel (ν : Measure X) [IsFiniteMeasure ν]
    {E : Set (X × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    let μ := (ν.prod volume).restrict E
    IsFiniteMeasure μ ∧ ∃ κ : Kernel X ℝ, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ ∧
      (∀ q : ENNReal, 0 < q →
        ∀ x ∈ Submission.Lib.K4Homogenization.durationRetained unitTimeReference
          (originalUnitEventDensity E) univ q, κ x ≤ (1 / q) • volume) ∧
      (∀ q : ENNReal, μ (Prod.fst ⁻¹'
        (Submission.Lib.K4Homogenization.durationRetained unitTimeReference
          (originalUnitEventDensity E) univ q)ᶜ) ≤ q * ν univ) := by
  letI : IsProbabilityMeasure unitTimeReference := unitTimeReference_probability
  obtain ⟨hfin, κ, hκ, hjoint, hcap, hshort⟩ :=
    Submission.Lib.K4ScalarActualSwitching.bounded_incidence_disintegration ν
      unitTimeReference (originalUnitEventDensity E) (originalUnitEventDensity_measurable hE)
      1 ENNReal.one_ne_top (originalUnitEventDensity_le_one E)
  rw [unit_event_withDensity ν hE hunit] at hfin hjoint hshort
  refine ⟨hfin, κ, hκ, hjoint, ?_, hshort⟩
  intro q hq x hx
  apply (hcap q hq x hx).trans
  exact smul_le_smul_left _ Measure.restrict_le_self

end Event

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
