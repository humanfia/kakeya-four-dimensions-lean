-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ClockBadSetTransport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SelectedPacketLaw

/-! A measurable exceptional set returns from the unit clock with its
relative original mass exactly preserved. The normalization denominator
uses the full original assignment and cancels from both sides. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open ParentSource.Broad.Source
open scoped ENNReal

noncomputable section

/-- Return a measurable bad set from a packet's unit clock. The desired
property can be an existential polynomial fit and need not be measurable. -/
theorem measurable_original_bad_set_of_clock
    (packet : FrozenPacket) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν packet.assigned ≠ 0)
    (S : Set Ev) (hS : MeasurableSet S) (hSF : S⊆packet.counted)
    (badClock : Set Ev) (hbad : MeasurableSet badClock)
    (property : Ev → Prop)
    (hqualified : ∀ w∈S, packet.timeChange w∉badClock → property w)
    (cap : ENNReal)
    (hcap : packet.selectedLaw ν S badClock ≤ cap*packet.selectedLaw ν S univ) :
    ∃ bad : Set Ev, MeasurableSet bad ∧
      {w | w∈S ∧ ¬property w}⊆bad ∧
      ((ν.prod volume).restrict S) bad ≤ cap*((ν.prod volume).restrict S) univ := by
  let bad := packet.timeChange ⁻¹' badClock
  have hbadOriginal : MeasurableSet bad := hbad.preimage packet.timeChange.measurable
  let denominator := ENNReal.ofReal packet.unitFrame.q*ν packet.assigned
  have hd0 : denominator≠0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr packet.unitFrame_length_pos).ne' hA
  have hdt : denominator≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)
  have hbadMass : packet.selectedLaw ν S badClock=
      denominator⁻¹*((ν.prod volume).restrict S) bad := by
    rw [packet.selectedLaw_original ν hA hS hSF,
      Measure.smul_apply,smul_eq_mul,
      Measure.map_apply packet.timeChange.measurable hbad]
  have htotal : packet.selectedLaw ν S univ=
      denominator⁻¹*((ν.prod volume).restrict S) univ := by
    rw [packet.selectedLaw_original ν hA hS hSF,
      Measure.smul_apply,smul_eq_mul,
      Measure.map_apply packet.timeChange.measurable MeasurableSet.univ,preimage_univ]
  rw [hbadMass,htotal] at hcap
  refine ⟨bad,hbadOriginal,?_,?_⟩
  · rintro w ⟨hw,hnot⟩
    by_contra hgood
    exact hnot (hqualified w hw hgood)
  · calc
      _ = denominator*(denominator⁻¹*((ν.prod volume).restrict S) bad) := by
        rw [←mul_assoc,ENNReal.mul_inv_cancel hd0 hdt,one_mul]
      _ ≤ denominator*(cap*(denominator⁻¹*((ν.prod volume).restrict S) univ)) :=
        mul_le_mul' le_rfl hcap
      _ = (denominator*denominator⁻¹)*(cap*((ν.prod volume).restrict S) univ) := by ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hd0 hdt,one_mul]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
