-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ClockGoodSourceTransport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockBadSetTransport

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open ParentSource.Broad.Source
open scoped ENNReal

noncomputable section

/-- Pull a measurable good source back from the unit clock. An absolute
unit-clock deletion is charged to the FULL original assignment times
its block length, before any descendant is selected. -/
theorem original_good_source_of_clock
    (packet : FrozenPacket) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν packet.assigned≠0)
    (S : Set Ev) (hS : MeasurableSet S) (hSF : S⊆packet.counted)
    (goodClock : Set Ev) (hgood : MeasurableSet goodClock)
    (loss : ENNReal)
    (hloss : ((packet.prior ν).prod volume) (packet.selectedEvent S\goodClock)≤loss) :
    ∃ good : Set Ev, MeasurableSet good ∧ good⊆S ∧
      packet.selectedEvent good=packet.selectedEvent S∩goodClock ∧
      (ν.prod volume) (S\good)≤loss*(ENNReal.ofReal packet.unitFrame.q*ν packet.assigned) := by
  let good := S∩packet.timeChange ⁻¹' goodClock
  have hgoodOriginal : MeasurableSet good := hS.inter (hgood.preimage packet.timeChange.measurable)
  have hgoodS : good⊆S := inter_subset_left
  have hselected : packet.selectedEvent good=packet.selectedEvent S∩goodClock := by
    ext z
    constructor
    · rintro ⟨w,⟨hw,hg⟩,rfl⟩
      exact ⟨⟨w,hw,rfl⟩,hg⟩
    · rintro ⟨⟨w,hw,rfl⟩,hg⟩
      exact ⟨w,⟨hw,hg⟩,rfl⟩
  let denominator := ENNReal.ofReal packet.unitFrame.q*ν packet.assigned
  have hd0 : denominator≠0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr packet.unitFrame_length_pos).ne' hA
  have hdt : denominator≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)
  have hbadSet : (packet.timeChange ⁻¹' goodClockᶜ)∩S=S\good := by
    ext z
    simp only [good,mem_inter_iff,mem_preimage,mem_compl_iff,mem_sdiff]
    tauto
  have hclock : packet.selectedLaw ν S goodClockᶜ=
      ((packet.prior ν).prod volume) (packet.selectedEvent S\goodClock) := by
    rw [FrozenPacket.selectedLaw,Measure.restrict_apply hgood.compl]
    congr 1
    ext z
    simp only [mem_inter_iff,mem_compl_iff,mem_sdiff]
    tauto
  have hscale : ((packet.prior ν).prod volume) (packet.selectedEvent S\goodClock)=
      denominator⁻¹*(ν.prod volume) (S\good) := by
    rw [←hclock,packet.selectedLaw_original ν hA hS hSF,
      Measure.smul_apply,smul_eq_mul,Measure.map_apply packet.timeChange.measurable hgood.compl,
      Measure.restrict_apply' hS,hbadSet]
  refine ⟨good,hgoodOriginal,hgoodS,hselected,?_⟩
  change (ν.prod volume) (S\good)≤loss*denominator
  calc
    _ = denominator*(denominator⁻¹*(ν.prod volume) (S\good)) := by
      rw [←mul_assoc,ENNReal.mul_inv_cancel hd0 hdt,one_mul]
    _ ≤ denominator*loss := mul_le_mul' le_rfl (hscale ▸ hloss)
    _ = _ := mul_comm _ _

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
