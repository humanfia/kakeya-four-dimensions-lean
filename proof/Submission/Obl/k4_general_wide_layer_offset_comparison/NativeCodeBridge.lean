-- Adapted from this LOT tree, obligation o254, branch x0898, commit 91a4f454, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeCodeBridge.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSlices
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomains

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

noncomputable section

def fullComparisonCode (tag : Fin 2 → ℤ) (D : ℤ × ℤ × ℤ) : Native.CommonDomain.Code :=
  ![D.1, tag 0, tag 1, D.2.1, D.2.2]

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

theorem fullComparisonCode_comparisonCode (k : ℕ) (m q g w : ℝ) (ω : α × ℝ) :
    fullComparisonCode (p.comparisonCode k m q g w ω).1 (p.comparisonCode k m q g w ω).2 =
      Native.CommonDomain.code q (p.N k ^ (-m)) g w (p.b k ω.1) ω.2 := by
  ext i
  fin_cases i <;> rfl

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
