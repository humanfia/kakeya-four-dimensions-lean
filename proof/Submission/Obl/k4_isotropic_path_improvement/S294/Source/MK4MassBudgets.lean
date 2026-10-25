-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.MK4MassBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.PostStateMassBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open scoped ENNReal

noncomputable section

/-- The original-reference MK4 charge at the literal one-quarter
retention choice and epsilon=kappa^-1/512. The renewal uses the same
cut as the final states, so its charge is already paid. -/
theorem original_mk4_mass_budget
    {κ cell duration : ℝ} {beta : ENNReal} (hκ : 0 < κ)
    (hcell : 0 ≤ cell) (hduration : 0 ≤ duration)
    (hrates : cell+duration ≤ κ⁻¹/256)
    (hbeta : 6561*beta ≤ ENNReal.ofReal (κ⁻¹/1024)) :
    ENNReal.ofReal ((1-(1/4:ℝ))⁻¹)*ENNReal.ofReal (κ⁻¹/512)+
      (ENNReal.ofReal cell+ENNReal.ofReal duration)+81*beta ≤
        ENNReal.ofReal (κ⁻¹/64) := by
  have hratesE : ENNReal.ofReal cell+ENNReal.ofReal duration ≤ ENNReal.ofReal (κ⁻¹/256) := by
    rw [←ENNReal.ofReal_add hcell hduration]
    exact ENNReal.ofReal_le_ofReal hrates
  have hrenewal : 81*beta ≤ ENNReal.ofReal (κ⁻¹/1024) :=
    (mul_le_mul' (by norm_num : (81:ENNReal) ≤ 6561) le_rfl).trans hbeta
  rw [show (1-(1/4:ℝ))⁻¹=4/3 by norm_num]
  calc
    _ ≤ ENNReal.ofReal (4/3:ℝ)*ENNReal.ofReal (κ⁻¹/512)+
        ENNReal.ofReal (κ⁻¹/256)+ENNReal.ofReal (κ⁻¹/1024) :=
      add_le_add (add_le_add le_rfl hratesE) hrenewal
    _ = ENNReal.ofReal ((4/3:ℝ)*(κ⁻¹/512)+κ⁻¹/256+κ⁻¹/1024) := by
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4/3)]
      repeat rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hh : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
      linarith only [hh])

/-- The literal state budgets supply the renewal charge without any
new cut, retained mass or choice of a front prediction exponent. -/
theorem original_mk4_mass_budget_of_states
    {N κ Krecord b front allowance entropy cell duration : ℝ}
    (hκ : 0 < κ) (hstates : RecordBudgets.StateBudgetsAt N κ Krecord b front allowance entropy)
    (hcell : 0 ≤ cell) (hduration : 0 ≤ duration)
    (hrates : cell+duration ≤ κ⁻¹/256) :
    ENNReal.ofReal ((1-(1/4:ℝ))⁻¹)*ENNReal.ofReal (κ⁻¹/512)+
      (ENNReal.ofReal cell+ENNReal.ofReal duration)+81*ENNReal.ofReal (N^(-b)) ≤
        ENNReal.ofReal (κ⁻¹/64) :=
  original_mk4_mass_budget hκ hcell hduration hrates hstates.state_loss

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
