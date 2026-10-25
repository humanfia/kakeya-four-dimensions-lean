import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ParentNativeSheets
import Submission.Obl.k4_general_parent_projected_layers.Support.ParentMass

namespace Submission.Obl.k4_narrow_projected_row_parents

open Submission.Obl.k4_general_parent_projected_layers
open Cmp.SheetComparison

/-- The two native-sheet discards with `A = 1` already fit a fixed fraction
of the model's mass floor when their filling constants dominate its loss. -/
theorem native_sheet_bad_budget {K F B : ℝ} (hK : 0 < K)
    (hF : 10000 * K ≤ F) (hB : 10000 * K ≤ B) :
    K * ((2 * K * F)⁻¹ + (2 * K * B)⁻¹) ≤ 1 / (10000 * K) := by
  have hFp : 0 < F := lt_of_lt_of_le (by positivity) hF
  have hBp : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hid : K * ((2 * K * F)⁻¹ + (2 * K * B)⁻¹) =
      (2 * F)⁻¹ + (2 * B)⁻¹ := by field_simp
  rw [hid]
  calc (2 * F)⁻¹ + (2 * B)⁻¹ ≤ (20000 * K)⁻¹ + (20000 * K)⁻¹ := by
         exact add_le_add (inv_anti₀ (by positivity) (by linarith))
           (inv_anti₀ (by positivity) (by linarith))
       _ = 1 / (10000 * K) := by field_simp; ring

/-- The actual parent filling constants are large enough pointwise. Thus the
native-sheet theorem may use one fixed integer `A = 1` at every index. -/
theorem native_parent_sheet_bad_budget {K a : ℝ} (hK : 1 ≤ K) (ha : 0 < a)
    (ha1 : a ≤ 1) :
    K * ((2 * K * parentFilling K a)⁻¹ + (2 * K * parentBinCap K)⁻¹) ≤
      1 / (10000 * K) := by
  apply native_sheet_bad_budget (zero_lt_one.trans_le hK)
  · have hK16 : K ≤ K ^ 16 := le_self_pow₀ hK (by norm_num)
    calc 10000 * K ≤ (2 * K) ^ 16 := by
           rw [mul_pow]
           norm_num
           nlinarith
         _ ≤ parentFilling K a := native_power_le_parentFilling hK ha ha1
  · have hK6 : K ≤ K ^ 6 := le_self_pow₀ hK (by norm_num)
    unfold parentBinCap
    nlinarith

end Submission.Obl.k4_narrow_projected_row_parents
