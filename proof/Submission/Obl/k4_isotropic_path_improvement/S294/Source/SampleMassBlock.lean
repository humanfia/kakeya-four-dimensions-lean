-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleMassBlock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeScaleData
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFinalMassReserve
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MK4MassBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open scoped ENNReal

noncomputable section

/-- The exact final sample reserve from the actual native scale data,
original record/state budgets, census charge and MK4 scalar rates.
The renewal and final states use the same original cut. -/
theorem sample_mass_block
    {q : NativeScaleDesign} {N sigma Kcensus stripWidth theta : ℝ} {T fine steps nfam R : ℕ}
    (native : NativeScaleData q N sigma T fine steps Kcensus stripWidth theta)
    {κ Krecord b front entropy θrow cellRate durationRate Vmax : ℝ} {δref : ENNReal}
    (hκ : 1 ≤ κ) (hκN : κ ≤ N^sigma)
    (hstates : RecordBudgets.StateBudgetsAt N κ Krecord b front q.display entropy)
    (hKcensus : 0 ≤ Kcensus) (hcellRate : 0 ≤ cellRate) (hdurationRate : 0 ≤ durationRate)
    (hVmax : 0 ≤ Vmax)
    (hrates : (Kcensus*((2:ℝ)^steps)^3)*cellRate+
      durationRate*(3*(1+24*κ+κ^2+Vmax)+3)*(7:ℝ)^4 ≤ κ⁻¹/256)
    (hcensus : (nfam:ENNReal)*(ENNReal.ofReal (4*Krecord^(3*R+28)*κ^2)*
      (ENNReal.ofReal (θrow*(Krecord^R)⁻¹)+27*(δref*ENNReal.ofReal (κ^2)))) ≤
        ENNReal.ofReal (κ⁻¹/64)) :
    let scales := native.scales
    let beta := ENNReal.ofReal (N^(-b))
    ENNReal.ofReal (1-(1/4:ℝ))⁻¹*
        (scales.regularityFactor*(ENNReal.ofReal (2/N^q.display)+10000*scales.nativeFailureBound)+
          scales.regularityFactor*scales.supportLoss+6561*beta+native.pre.charge)+
      ((nfam:ENNReal)*(ENNReal.ofReal (4*Krecord^(3*R+28)*κ^2)*
          (ENNReal.ofReal (θrow*(Krecord^R)⁻¹)+27*(δref*ENNReal.ofReal (κ^2))))+
        (ENNReal.ofReal (1-(1/4:ℝ))⁻¹*ENNReal.ofReal (κ⁻¹/512)+
          (ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*cellRate)+
            ENNReal.ofReal (durationRate*(3*(1+24*κ+κ^2+Vmax)+3)*(7:ℝ)^4))+81*beta))+
      ENNReal.ofReal (N^(-b))*(⌈Krecord^12⌉₊:ENNReal)+ENNReal.ofReal (κ⁻¹/64) ≤
        ENNReal.ofReal (71*κ⁻¹/512) := by
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  have hmk4 := original_mk4_mass_budget_of_states hκpos hstates (by positivity) (by positivity) hrates
  have hfrac : ENNReal.ofReal ((1-(1/4:ℝ))⁻¹)=ENNReal.ofReal (1-(1/4:ℝ))⁻¹ := by norm_num
  rw [hfrac] at hmk4
  exact sample_final_mass_reserve hκpos (by norm_num)
    (native.terminal_charge κ hκ hκN) (native.support_charge κ hκ hκN) hstates.state_loss
    (native.pre_charge κ hκ hκN) hcensus hmk4 hstates.record_loss

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
