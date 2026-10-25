-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeNumeratorPowerBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

/-- The native spatial-entry cap is paid by the canonical numerator,
the fixed original entry cut and the chosen cap power. -/
theorem native_numerator_power_bound {N e C : ℝ} (hN : 1 ≤ N) (he : 0 ≤ e)
    (hconstant : 625 ≤ N^e) (hC : 0 ≤ C) (hCbound : C ≤ N^e) :
    625*C/N^(-4*e) ≤ N^(8*e) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  calc
    _ ≤ (N^e*N^e)/N^(-4*e) :=
      div_le_div_of_nonneg_right (mul_le_mul hconstant hCbound hC (by positivity)) (by positivity)
    _ = N^(6*e) := by
      rw [←Real.rpow_add hNp,←Real.rpow_sub hNp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
