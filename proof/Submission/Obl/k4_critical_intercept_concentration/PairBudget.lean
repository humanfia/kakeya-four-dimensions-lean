/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/PairBudget.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_intercept_concentration.DescendantCount

namespace Submission.Obl.k4_critical_intercept_concentration

open Finset

/-- The fourth power from true descendant counting cancels the fourth-power
volume of each descendant domain. The working mesh appears only as ω³. -/
theorem occupied_pair_budget_cancel {ι β : Type*} [DecidableEq β]
    (S : Finset ι) (G : ι → Finset β) (F : Finset β)
    {K C q qp D ω : ℝ} (_hK : 0 ≤ K) (hC : 0 ≤ C)
    (hq : 0 < q) (hqp : 0 < qp) (_hD : 0 ≤ D) (hω : 0 < ω)
    (hcount : (S.card : ℝ) ≤ K ^ 2 * (qp / q) ^ 4 * D)
    (hcover : F ⊆ S.biUnion G)
    (hlocal : ∀ i ∈ S, ((G i).card : ℝ) ≤ C * (q / qp) ^ 4 / ω ^ 3) :
    (F.card : ℝ) * ω ^ 3 ≤ C * K ^ 2 * D := by
  have hcard : (F.card : ℝ) ≤ ∑ i ∈ S, ((G i).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hupper : (F.card : ℝ) ≤
      (S.card : ℝ) * (C * (q / qp) ^ 4 / ω ^ 3) := by
    calc
      _ ≤ ∑ i ∈ S, ((G i).card : ℝ) := hcard
      _ ≤ ∑ _i ∈ S, C * (q / qp) ^ 4 / ω ^ 3 := Finset.sum_le_sum hlocal
      _ = _ := by simp
  calc
    (F.card : ℝ) * ω ^ 3 ≤
        ((S.card : ℝ) * (C * (q / qp) ^ 4 / ω ^ 3)) * ω ^ 3 := by gcongr
    _ ≤ (K ^ 2 * (qp / q) ^ 4 * D) * (C * (q / qp) ^ 4 / ω ^ 3) * ω ^ 3 := by
      gcongr
    _ = C * K ^ 2 * D := by field_simp

end Submission.Obl.k4_critical_intercept_concentration
