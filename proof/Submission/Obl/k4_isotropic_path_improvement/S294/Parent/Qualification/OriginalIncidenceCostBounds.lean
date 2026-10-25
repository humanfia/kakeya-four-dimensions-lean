-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalIncidenceCostBounds, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalIncidenceData

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

section Costs

variable {Λ : Type} [MeasurableSpace Λ] {ν : Measure Λ} {μ : Measure (Λ × ℝ)}
    {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {b ρ H Krow η error ζ dimension Kss Htarget Kcap profileAmplitude : ℝ}
    {paletteRef : Measure (Fin 2 → ℝ)}
    (data : OriginalIncidenceData ν μ c E b ρ H Krow η error ζ dimension Kss Htarget Kcap profileAmplitude paletteRef)

/-- An original probability prior and a unit-time current source need
no source-dependent mass in their error budget. -/
def OriginalIncidenceData.unitMassResidualEntryLoss : ENNReal :=
  (∑ i : Fin data.L, ENNReal.ofReal (data.cut i.val)*
    (⌈256*(12*H+4)^7*(data.C0*data.K0/data.entryCut0)⌉₊*256:ℕ))+
  (ENNReal.ofReal (data.entryCut0*zoomBlockVisitConstant)+
    ∑ i : Fin data.L, ENNReal.ofReal (data.entryCut i.val*zoomBlockVisitConstant))

/-- The uniform source-mass-free version of the literal native error. -/
def OriginalIncidenceData.unitMassNativeFailureBound : ENNReal :=
  ((parameterLevel ζ+1:ℕ):ENNReal)*ENNReal.ofReal (data.nativeCut*zoomBlockVisitConstant)+
    data.selectionFactor*ENNReal.ofReal (2*data.N^(-(data.ch*data.alpha)))+
      data.unitMassResidualEntryLoss

include data

theorem OriginalIncidenceData.residualEntryLoss_le_unitMass
    (hμ : μ univ ≤ 1) (hν : ν univ ≤ 1) :
    data.residualEntryLoss ≤ data.unitMassResidualEntryLoss := by
  unfold OriginalIncidenceData.residualEntryLoss OriginalIncidenceData.unitMassResidualEntryLoss
  apply add_le_add
  · exact (mul_le_mul' le_rfl hμ).trans_eq (mul_one _)
  · exact (mul_le_mul' le_rfl hν).trans_eq (mul_one _)

theorem OriginalIncidenceData.nativeFailureBound_le_unitMass
    (hμ : μ univ ≤ 1) (hν : ν univ ≤ 1) :
    data.nativeFailureBound ≤ data.unitMassNativeFailureBound := by
  exact add_le_add le_rfl (data.residualEntryLoss_le_unitMass hμ hν)

end Costs

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
