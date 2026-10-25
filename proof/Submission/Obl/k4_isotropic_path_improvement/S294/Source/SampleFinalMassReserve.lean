-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleFinalMassReserve, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.PostStateMassBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open scoped ENNReal

noncomputable section

/-- The literal final sample reserve follows from the separately paid
original-reference charges. The multiplicative MK4 loss is included
before the native and post-state charges, as in `sample_final`. -/
theorem sample_final_mass_reserve
    {κ : ℝ} (hκ : 0 < κ)
    {cfrac terminal chargeR states chargeN census mk4 records : ENNReal}
    (hcfrac : cfrac ≤ ENNReal.ofReal (4/3:ℝ))
    (hterminal : terminal ≤ ENNReal.ofReal (κ⁻¹/1024))
    (hchargeR : chargeR ≤ ENNReal.ofReal (κ⁻¹/1024))
    (hstates : states ≤ ENNReal.ofReal (κ⁻¹/1024))
    (hchargeN : chargeN ≤ ENNReal.ofReal (κ⁻¹/64))
    (hcensus : census ≤ ENNReal.ofReal (κ⁻¹/64))
    (hmk4 : mk4 ≤ ENNReal.ofReal (κ⁻¹/64))
    (hrecords : records ≤ ENNReal.ofReal (κ⁻¹/1024)) :
    cfrac*(terminal+chargeR+states+chargeN)+(census+mk4)+records+
      ENNReal.ofReal (κ⁻¹/64) ≤ ENNReal.ofReal (71*κ⁻¹/512) := by
  have hκinv : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  calc
    _ ≤ ENNReal.ofReal (4/3:ℝ)*
        (ENNReal.ofReal (κ⁻¹/1024)+ENNReal.ofReal (κ⁻¹/1024)+
          ENNReal.ofReal (κ⁻¹/1024)+ENNReal.ofReal (κ⁻¹/64))+
        (ENNReal.ofReal (κ⁻¹/64)+ENNReal.ofReal (κ⁻¹/64))+
        ENNReal.ofReal (κ⁻¹/1024)+ENNReal.ofReal (κ⁻¹/64) := by
      gcongr
    _ = ENNReal.ofReal ((4/3:ℝ)*(κ⁻¹/1024+κ⁻¹/1024+κ⁻¹/1024+κ⁻¹/64)+
        (κ⁻¹/64+κ⁻¹/64)+κ⁻¹/1024+κ⁻¹/64) := by
      repeat rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4/3)]
      repeat rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith only [hκinv])

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
