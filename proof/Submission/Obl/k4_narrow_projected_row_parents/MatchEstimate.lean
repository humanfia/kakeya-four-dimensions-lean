import Submission.Obl.k4_narrow_projected_row_parents.Model
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ComparisonTables

namespace Submission.Obl.k4_narrow_projected_row_parents

/-- The frozen Match hypothesis supplies the estimate used by the finite
comparison tables. This is the defining conclusion of the imported sheet comparison. -/
theorem comparison_estimate_of_match (hMatch : Match) (D : ℕ) (hD : 1 ≤ D)
    (d : ℝ) (hd : 0 ≤ d) (hd1 : d < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 1 ≤ C ∧ Cmp.SheetComparison.ComparisonEstimate D d ε C := by
  exact Cmp.SheetComparison.sheet_comparison hMatch D hD d hd hd1

end Submission.Obl.k4_narrow_projected_row_parents
