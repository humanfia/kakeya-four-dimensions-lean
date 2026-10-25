-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.FrozenPacketLaw, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/FrozenPacketLaw.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/FrozenPacketLaw.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 38d075b9;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenPacketLaw.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacketGeometry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnitIncidenceKernel
import Submission.Obl.k4_balanced_native_packet_transport.CPF.TimeConditioning

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Change time only. Keeping the original line as the trajectory index
lets the geometric functions in FrozenPacketGeometry refer to that same line. -/
def timeChange (p : FrozenPacket) : Incidence ≃ᵐ Incidence :=
  Submission.Obl.k4_balanced_native_packet_transport.CPF.normalizedIncidenceEquiv
    (MeasurableEquiv.refl Line) p.unitFrame.t₀ p.unitFrame.q p.unitFrame_length_pos.ne'

theorem timeChange_apply (p : FrozenPacket) (z : Incidence) :
    p.timeChange z = (z.1, p.unitFrame.q⁻¹ * (z.2 - p.unitFrame.t₀)) := by
  apply Prod.ext rfl
  exact Submission.Obl.k4_balanced_native_packet_transport.CPF.timeChartEquiv_symm_apply
    p.unitFrame.t₀ p.unitFrame.q p.unitFrame_length_pos.ne' z.2

/-- The FULL original assignment supplies the prior denominator. -/
def prior (p : FrozenPacket) (ν : Measure Line) : Measure Line :=
  Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior
    ν p.assigned (MeasurableEquiv.refl Line)

theorem prior_eq (p : FrozenPacket) (ν : Measure Line) :
    p.prior ν = (ν p.assigned)⁻¹ • ν.restrict p.assigned := by
  unfold prior Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior
  change _ • Measure.map id _ = _
  rw [Measure.map_id]

theorem prior_probability (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) : IsProbabilityMeasure (p.prior ν) :=
  Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior_probability
    ν p.assigned (MeasurableEquiv.refl Line) hA (measure_ne_top _ _)

def event (p : FrozenPacket) : Set Incidence := p.timeChange '' p.counted

theorem measurable_event (p : FrozenPacket) : MeasurableSet p.event :=
  p.timeChange.measurableSet_image.mpr p.measurable_counted

theorem event_unit_time (p : FrozenPacket) : p.event ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  apply Submission.Obl.k4_balanced_native_packet_transport.CPF.normalized_event_unit_time
    (MeasurableEquiv.refl Line) p.unitFrame.t₀ p.unitFrame.q p.unitFrame_length_pos p.counted
  intro z hz
  exact ⟨mem_univ _, (p.counted_inside_original hz).2.2⟩

theorem event_assignment (p : FrozenPacket) {z : Incidence} (hz : z ∈ p.event) :
    z.1 ∈ p.assigned := by
  obtain ⟨z, hz, rfl⟩ := hz
  exact (p.counted_inside_original hz).2.1

def law (p : FrozenPacket) (ν : Measure Line) : Measure Incidence :=
  ((p.prior ν).prod volume).restrict p.event

theorem law_mass_le_one (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) : p.law ν univ ≤ 1 := by
  letI : IsProbabilityMeasure (p.prior ν) := p.prior_probability ν hA
  change (((p.prior ν).prod volume).restrict p.event) univ ≤ 1
  rw [Measure.restrict_apply_univ]
  calc
    _ ≤ ((p.prior ν).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) :=
      measure_mono p.event_unit_time
    _ = 1 := by simp [Measure.prod_prod, Real.volume_Icc]

/-- The normalized law is exactly the old selected incidence law divided
by old time length times FULL old assignment mass. -/
theorem law_original (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) :
    p.law ν = (ENNReal.ofReal p.unitFrame.q * ν p.assigned)⁻¹ •
      (((ν.prod volume).restrict p.counted).map p.timeChange) := by
  apply Submission.Obl.k4_balanced_native_packet_transport.CPF.selected_product_transport
    ν p.assigned p.counted p.measurable_counted _ (MeasurableEquiv.refl Line)
      p.unitFrame.t₀ p.unitFrame.q p.unitFrame_length_pos hA (measure_ne_top _ _)
  intro z hz
  exact ⟨(p.counted_inside_original hz).2.1, mem_univ _⟩

theorem law_mass_original (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) :
    p.law ν univ = (ENNReal.ofReal p.unitFrame.q * ν p.assigned)⁻¹ *
      (ν.prod volume) p.counted := by
  rw [p.law_original ν hA, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply p.timeChange.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

/-- A true packet's original saturation budget gives the lower mass of
its normalized law. The denominator remains the full assignment. -/
theorem law_mass_lower_of_original_budget (p : FrozenPacket) (ν : Measure Line)
    [IsFiniteMeasure ν] (hA : ν p.assigned ≠ 0) (hκ : 0 < p.slack)
    (hbudget : ENNReal.ofReal p.unitFrame.q * ν p.assigned ≤
      ENNReal.ofReal (p.slack ^ 2) * (ν.prod volume) p.counted) :
    (ENNReal.ofReal (p.slack ^ 2))⁻¹ ≤ p.law ν univ := by
  let B := ENNReal.ofReal p.unitFrame.q * ν p.assigned
  let C := ENNReal.ofReal (p.slack ^ 2)
  have hB0 : B ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr p.unitFrame_length_pos).ne' hA
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hκ)).ne'
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [p.law_mass_original ν hA]
  change C⁻¹ ≤ B⁻¹ * (ν.prod volume) p.counted
  calc
    C⁻¹ = (C⁻¹ * B⁻¹) * B := by rw [mul_assoc, ENNReal.inv_mul_cancel hB0 hBt, mul_one]
    _ ≤ (C⁻¹ * B⁻¹) * (C * (ν.prod volume) p.counted) := mul_le_mul' le_rfl hbudget
    _ = (C⁻¹ * C) * (B⁻¹ * (ν.prod volume) p.counted) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hC0 hCt, one_mul]

theorem law_original_assignment (p : FrozenPacket) (ν : Measure Line) :
    ∀ᵐ z ∂p.law ν, z.1 ∈ p.assigned :=
  (ae_restrict_mem p.measurable_event).mono (fun _ hz => p.event_assignment hz)

/-- The genuine Markov time kernel of this same original packet event.
The short-line budget is charged to the full old conditional prior. -/
theorem law_time_kernel (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) :
    IsFiniteMeasure (p.law ν) ∧
      ∃ κ : Kernel Line ℝ, IsMarkovKernel κ ∧ (p.law ν).fst ⊗ₘ κ = p.law ν ∧
      (∀ q : ENNReal, 0 < q →
        ∀ l ∈ Submission.Lib.K4Homogenization.durationRetained unitTimeReference
          (originalUnitEventDensity p.event) univ q, κ l ≤ (1 / q) • volume) ∧
      (∀ q : ENNReal, p.law ν (Prod.fst ⁻¹'
        (Submission.Lib.K4Homogenization.durationRetained unitTimeReference
          (originalUnitEventDensity p.event) univ q)ᶜ) ≤ q) := by
  letI : IsProbabilityMeasure (p.prior ν) := p.prior_probability ν hA
  obtain ⟨hfin, κ, hκ, hlaw, hcap, hshort⟩ := original_unit_event_time_kernel
    (p.prior ν) p.measurable_event p.event_unit_time
  refine ⟨hfin, κ, hκ, hlaw, hcap, ?_⟩
  intro q
  simpa only [law, measure_univ, mul_one] using hshort q

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket
