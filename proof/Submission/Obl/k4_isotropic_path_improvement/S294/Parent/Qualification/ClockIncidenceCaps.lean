-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ClockIncidenceCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockGoodSourceTransport

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open ParentSource.Broad.Source
open scoped ENNReal

noncomputable section

/-- The full original packet reference cancels exactly when a current
numerator is moved to the unit clock. The palette weight may be included
in `cap`, and is not reconditioned. -/
theorem selected_clock_cap_of_original
    (packet : FrozenPacket) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν packet.assigned≠0) (S : Set Ev) (hS : MeasurableSet S) (hSF : S⊆packet.counted)
    (B : Set Ev) (hB : MeasurableSet B) (cap : ENNReal)
    (hcap : ((ν.prod volume).restrict S) (packet.timeChange ⁻¹' B)≤
      cap*(ENNReal.ofReal packet.unitFrame.q*ν packet.assigned)) :
    packet.selectedLaw ν S B≤cap := by
  let denominator := ENNReal.ofReal packet.unitFrame.q*ν packet.assigned
  have hd0 : denominator≠0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr packet.unitFrame_length_pos).ne' hA
  have hdt : denominator≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)
  rw [packet.selectedLaw_original ν hA hS hSF,
    Measure.smul_apply,smul_eq_mul,Measure.map_apply packet.timeChange.measurable hB]
  apply (mul_le_mul' le_rfl hcap).trans_eq
  change denominator⁻¹*(cap*denominator)=cap
  rw [mul_left_comm,ENNReal.inv_mul_cancel hd0 hdt,mul_one]

/-- Actual sourcewise coordinate equality suffices to transfer a cap;
no replacement of the original measure or source reference is needed. -/
theorem selected_clock_coordinate_cap_of_original {X : Type*} [MeasurableSpace X]
    (packet : FrozenPacket) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν packet.assigned≠0) (S : Set Ev) (hS : MeasurableSet S) (hSF : S⊆packet.counted)
    (clock original : Ev → X) (hclock : Measurable clock)
    (hcoordinates : ∀ z∈S, clock (packet.timeChange z)=original z)
    (B : Set X) (hB : MeasurableSet B) (cap : ENNReal)
    (hcap : ((ν.prod volume).restrict S) (original ⁻¹' B)≤
      cap*(ENNReal.ofReal packet.unitFrame.q*ν packet.assigned)) :
    packet.selectedLaw ν S (clock ⁻¹' B)≤cap := by
  apply selected_clock_cap_of_original packet ν hA S hS hSF (clock ⁻¹' B) (hclock hB) cap
  apply le_trans (le_of_eq ?_) hcap
  apply measure_congr
  filter_upwards [ae_restrict_mem hS] with z hz
  simp only [mem_preimage,hcoordinates z hz]


/-- Exact coordinate transport on an arbitrary selected original source.
The denominator is the full ancestor assignment and clock. -/
theorem selected_clock_coordinate_measure_eq_original {X : Type*} [MeasurableSpace X]
    (packet : FrozenPacket) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν packet.assigned≠0) (S : Set Ev) (hS : MeasurableSet S) (hSF : S⊆packet.counted)
    (clock original : Ev → X) (hclock : Measurable clock)
    (hcoordinates : ∀ z∈S, clock (packet.timeChange z)=original z)
    (B : Set X) (hB : MeasurableSet B) :
    packet.selectedLaw ν S (clock ⁻¹' B)=
      (ENNReal.ofReal packet.unitFrame.q*ν packet.assigned)⁻¹*
        ((ν.prod volume).restrict S) (original ⁻¹' B) := by
  rw [packet.selectedLaw_original ν hA hS hSF,
    Measure.smul_apply,smul_eq_mul,Measure.map_apply packet.timeChange.measurable (hclock hB)]
  congr 1
  apply measure_congr
  filter_upwards [ae_restrict_mem hS] with z hz
  simp only [mem_preimage,hcoordinates z hz]

/-- Conditional ratios survive an exact clock change at the same
original numerator and denominator; no conditional law is replaced. -/
theorem selected_clock_coordinate_ratio_of_original {X : Type*} [MeasurableSpace X]
    (packet : FrozenPacket) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν packet.assigned≠0) (S : Set Ev) (hS : MeasurableSet S) (hSF : S⊆packet.counted)
    (clock original : Ev → X) (hclock : Measurable clock)
    (hcoordinates : ∀ z∈S, clock (packet.timeChange z)=original z)
    (B D : Set X) (hB : MeasurableSet B) (hD : MeasurableSet D) (cap : ENNReal)
    (hcap : ((ν.prod volume).restrict S) (original ⁻¹' B)≤
      cap*((ν.prod volume).restrict S) (original ⁻¹' D)) :
    packet.selectedLaw ν S (clock ⁻¹' B)≤cap*packet.selectedLaw ν S (clock ⁻¹' D) := by
  rw [selected_clock_coordinate_measure_eq_original packet ν hA S hS hSF clock original hclock hcoordinates B hB,
    selected_clock_coordinate_measure_eq_original packet ν hA S hS hSF clock original hclock hcoordinates D hD]
  exact (mul_le_mul' le_rfl hcap).trans_eq (by ac_rfl)


/-- An additive selected-law loss returns to the original law with
exactly the full old assignment-times-clock reference. -/
theorem original_mass_bound_of_selected_mass_bound
    (packet : FrozenPacket) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν packet.assigned≠0)
    (S keep : Set Ev) (hS : MeasurableSet S) (hkeep : MeasurableSet keep)
    (hSF : S⊆packet.counted) (hkeepS : keep⊆S) (loss : ENNReal)
    (hmass : packet.selectedLaw ν S univ≤packet.selectedLaw ν keep univ+loss) :
    (ν.prod volume) S≤(ν.prod volume) keep+
      loss*(ENNReal.ofReal packet.unitFrame.q*ν packet.assigned) := by
  let denominator := ENNReal.ofReal packet.unitFrame.q*ν packet.assigned
  have hd0 : denominator≠0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr packet.unitFrame_length_pos).ne' hA
  have hdt : denominator≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)
  rw [packet.selectedLaw_mass_original ν hA hS hSF,
    packet.selectedLaw_mass_original ν hA hkeep (hkeepS.trans hSF)] at hmass
  change denominator⁻¹*(ν.prod volume) S≤denominator⁻¹*(ν.prod volume) keep+loss at hmass
  change (ν.prod volume) S≤(ν.prod volume) keep+loss*denominator
  calc
    _ = denominator*(denominator⁻¹*(ν.prod volume) S) := by
      rw [←mul_assoc,ENNReal.mul_inv_cancel hd0 hdt,one_mul]
    _ ≤ denominator*(denominator⁻¹*(ν.prod volume) keep+loss) := mul_le_mul' le_rfl hmass
    _ = _ := by
      rw [mul_add,←mul_assoc,ENNReal.mul_inv_cancel hd0 hdt,one_mul,mul_comm denominator loss]


/-- An absolute clock exception returns to the original incidence law
with the full old reference and no selected-source denominator. -/
theorem original_event_bound_of_selected_bound
    (packet : FrozenPacket) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν packet.assigned≠0) (S : Set Ev) (hS : MeasurableSet S) (hSF : S⊆packet.counted)
    (B : Set Ev) (hB : MeasurableSet B) (loss : ENNReal)
    (hbound : packet.selectedLaw ν S B≤loss) :
    ((ν.prod volume).restrict S) (packet.timeChange ⁻¹' B)≤
      loss*(ENNReal.ofReal packet.unitFrame.q*ν packet.assigned) := by
  let denominator := ENNReal.ofReal packet.unitFrame.q*ν packet.assigned
  have hd0 : denominator≠0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr packet.unitFrame_length_pos).ne' hA
  have hdt : denominator≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)
  rw [packet.selectedLaw_original ν hA hS hSF,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply packet.timeChange.measurable hB] at hbound
  change denominator⁻¹*((ν.prod volume).restrict S) (packet.timeChange ⁻¹' B)≤loss at hbound
  calc
    _ = denominator*(denominator⁻¹*((ν.prod volume).restrict S) (packet.timeChange ⁻¹' B)) := by
      rw [←mul_assoc,ENNReal.mul_inv_cancel hd0 hdt,one_mul]
    _ ≤ denominator*loss := mul_le_mul' le_rfl hbound
    _ = _ := mul_comm _ _


/-- Multiplicative selection and additive clock loss return together
with the exact unchanged full original reference. -/
theorem original_scaled_mass_bound_of_selected_mass_bound
    (packet : FrozenPacket) (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν packet.assigned≠0)
    (S keep : Set Ev) (hS : MeasurableSet S) (hkeep : MeasurableSet keep)
    (hSF : S⊆packet.counted) (hkeepS : keep⊆S) (factor loss : ENNReal)
    (hmass : packet.selectedLaw ν S univ≤factor*packet.selectedLaw ν keep univ+loss) :
    (ν.prod volume) S≤factor*(ν.prod volume) keep+
      loss*(ENNReal.ofReal packet.unitFrame.q*ν packet.assigned) := by
  let denominator := ENNReal.ofReal packet.unitFrame.q*ν packet.assigned
  have hd0 : denominator≠0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr packet.unitFrame_length_pos).ne' hA
  have hdt : denominator≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν _)
  rw [packet.selectedLaw_mass_original ν hA hS hSF,
    packet.selectedLaw_mass_original ν hA hkeep (hkeepS.trans hSF)] at hmass
  change denominator⁻¹*(ν.prod volume) S≤factor*(denominator⁻¹*(ν.prod volume) keep)+loss at hmass
  change (ν.prod volume) S≤factor*(ν.prod volume) keep+loss*denominator
  calc
    _ = denominator*(denominator⁻¹*(ν.prod volume) S) := by
      rw [←mul_assoc,ENNReal.mul_inv_cancel hd0 hdt,one_mul]
    _ ≤ denominator*(factor*(denominator⁻¹*(ν.prod volume) keep)+loss) := mul_le_mul' le_rfl hmass
    _ = _ := by
      rw [mul_add,mul_left_comm denominator factor,←mul_assoc denominator,
        ENNReal.mul_inv_cancel hd0 hdt,one_mul,mul_comm denominator loss]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
