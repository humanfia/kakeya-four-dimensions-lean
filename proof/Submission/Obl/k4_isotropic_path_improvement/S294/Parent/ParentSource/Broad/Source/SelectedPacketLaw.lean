-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.SelectedPacketLaw, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/SelectedPacketLaw.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/SelectedPacketLaw.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacketLaw

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket

open MeasureTheory Set
open ProbabilityTheory
open scoped ENNReal
open scoped ProbabilityTheory

noncomputable section

/-- A measurable original source may be selected inside the whole chart.
It need not be the counted set of a new semialgebraic chart. -/
def selectedEvent (p : FrozenPacket) (J : Set Incidence) : Set Incidence := p.timeChange '' J

def selectedLaw (p : FrozenPacket) (ν : Measure Line) (J : Set Incidence) : Measure Incidence :=
  ((p.prior ν).prod volume).restrict (p.selectedEvent J)

theorem measurable_selectedEvent (p : FrozenPacket) {J : Set Incidence} (hJ : MeasurableSet J) :
    MeasurableSet (p.selectedEvent J) := p.timeChange.measurableSet_image.mpr hJ

theorem selectedEvent_subset (p : FrozenPacket) {J : Set Incidence} (hJ : J ⊆ p.counted) :
    p.selectedEvent J ⊆ p.event := image_mono hJ

theorem selectedLaw_le (p : FrozenPacket) (ν : Measure Line) {J : Set Incidence}
    (hJ : J ⊆ p.counted) : p.selectedLaw ν J ≤ p.law ν :=
  Measure.restrict_mono_set _ (p.selectedEvent_subset hJ)

theorem selectedLaw_le_product (p : FrozenPacket) (ν : Measure Line) (J : Set Incidence) :
    p.selectedLaw ν J ≤ (p.prior ν).prod volume := Measure.restrict_le_self

/-- Exact original transport of an arbitrary selected source; the
denominator remains the full old assignment times its old block length. -/
theorem selectedLaw_original (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) {J : Set Incidence} (hJ : MeasurableSet J)
    (hsub : J ⊆ p.counted) :
    p.selectedLaw ν J = (ENNReal.ofReal p.unitFrame.q * ν p.assigned)⁻¹ •
      (((ν.prod volume).restrict J).map p.timeChange) := by
  apply Submission.Obl.k4_balanced_native_packet_transport.CPF.selected_product_transport
    ν p.assigned J hJ _ (MeasurableEquiv.refl Line)
      p.unitFrame.t₀ p.unitFrame.q p.unitFrame_length_pos hA (measure_ne_top _ _)
  intro z hz
  exact ⟨(p.counted_inside_original (hsub hz)).2.1, mem_univ _⟩

theorem selectedLaw_mass_original (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) {J : Set Incidence} (hJ : MeasurableSet J)
    (hsub : J ⊆ p.counted) :
    p.selectedLaw ν J univ = (ENNReal.ofReal p.unitFrame.q * ν p.assigned)⁻¹ *
      (ν.prod volume) J := by
  rw [p.selectedLaw_original ν hA hJ hsub, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply p.timeChange.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

/-- Relative original mass is exactly normalized by that fixed budget. -/
theorem selectedLaw_mass_lower (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) {J : Set Incidence} (hJ : MeasurableSet J)
    (hsub : J ⊆ p.counted) {a : ENNReal}
    (hmass : a * (ENNReal.ofReal p.unitFrame.q * ν p.assigned) ≤ (ν.prod volume) J) :
    a ≤ p.selectedLaw ν J univ := by
  let B := ENNReal.ofReal p.unitFrame.q * ν p.assigned
  have hB0 : B ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr p.unitFrame_length_pos).ne' hA
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [p.selectedLaw_mass_original ν hA hJ hsub]
  change a ≤ B⁻¹ * (ν.prod volume) J
  calc
    a = B⁻¹ * (a * B) := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel hB0 hBt, mul_one]
    _ ≤ _ := mul_le_mul' le_rfl hmass

/-- The selected original event has its own genuine conditional time
kernel. Ordinary short-line loss is charged to the unchanged full prior. -/
theorem selectedLaw_time_kernel (p : FrozenPacket) (ν : Measure Line) [IsFiniteMeasure ν]
    (hA : ν p.assigned ≠ 0) {J : Set Incidence} (hJ : MeasurableSet J)
    (hsub : J ⊆ p.counted) :
    IsFiniteMeasure (p.selectedLaw ν J) ∧
      ∃ κ : Kernel Line ℝ, IsMarkovKernel κ ∧
        (p.selectedLaw ν J).fst ⊗ₘ κ = p.selectedLaw ν J ∧
        (∀ q : ENNReal, 0 < q →
          ∀ l ∈ Submission.Lib.K4Homogenization.durationRetained unitTimeReference
            (originalUnitEventDensity (p.selectedEvent J)) univ q, κ l ≤ (1 / q) • volume) ∧
        (∀ q : ENNReal, p.selectedLaw ν J (Prod.fst ⁻¹'
          (Submission.Lib.K4Homogenization.durationRetained unitTimeReference
            (originalUnitEventDensity (p.selectedEvent J)) univ q)ᶜ) ≤ q) := by
  letI : IsProbabilityMeasure (p.prior ν) := p.prior_probability ν hA
  obtain ⟨hfin, κ, hκ, hlaw, hcap, hshort⟩ := original_unit_event_time_kernel
    (p.prior ν) (p.measurable_selectedEvent hJ)
    ((p.selectedEvent_subset hsub).trans p.event_unit_time)
  refine ⟨hfin, κ, hκ, hlaw, hcap, ?_⟩
  intro q
  simpa only [selectedLaw, measure_univ, mul_one] using hshort q

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket
