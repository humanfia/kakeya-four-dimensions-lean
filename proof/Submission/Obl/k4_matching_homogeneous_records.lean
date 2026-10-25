import Submission.Obl.k4_matching_homogeneous_records.RawCofinal
import Submission.Obl.k4_matching_homogeneous_records.SelectionGlue
import Submission.Obl.k4_matching_homogeneous_records.Finalize
import Submission.Obl.k4_matching_profile_compactness

namespace Submission

open Obl.k4_matching_homogeneous_records

theorem k4_matching_homogeneous_records :
    ∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → ∀ β : ℕ → ℝ,
      ((∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2) ∧
        (∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ β j = 0)) →
      (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R →
        ∃ N : ℝ, R ≤ N ∧ Gap J d β ε N) →
      ∀ q : ℕ, 1 ≤ q → ∃ u : ℕ → ℝ,
        ((∀ k : ℕ, k ≤ q → 0 ≤ u k) ∧
          (∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b) ∧
          u q ≤ d + radius J β 1) ∧
        (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R →
          ∃ N : ℝ, R ≤ N ∧ Records J d β q u ε N) := by
  intro D J hD hDJ d hd β hβ hgap q hq
  have hs : 0 ≤ d + radius J β 1 :=
    add_nonneg hd (radius_nonneg hDJ.le hβ.2 (by norm_num))
  have compactness : CompactnessStatement := k4_matching_profile_compactness
  apply compactness q (d + radius J β 1) hs (Records J d β q)
  · exact records_stable
  · exact cofinal_selected_direct hs
      (cofinal_rawRecords hD hDJ.le hβ.2 hgap q hq)

end Submission
