import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Candidates
import Submission.Obl.k4_quadratic_finite_greedy_cover.PriorityFormat

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open Set
open Submission.Obl.k4_quadratic_finite_greedy_cover (selectedUnion fmt_congr fmt_empty fmt_biUnion fmt_diff)
noncomputable section

/-- A mixed priority history has format cost linear in its length, independently
of the analytical incidence masks used to discover it. -/
theorem mixed_priority_format {α β : Type*} (S : Finset α)
    (parent : α → β) (piece E : α → Set Trajectory) (H : ℝ) (D : ℕ) (hH : 0 ≤ H)
    (hE : ∀ a ∈ S, ∀ q, fmt 6 H D {w | (q,w) ∈ E a})
    (a : α) (ha : a ∈ S) (P : Finset α) (hP : P ⊆ S)
    (hrep : piece a = E a \ selectedUnion P parent E (parent a)) (q : ℕ) :
    fmt 6 (((S.card : ℝ) + 1) * H) D {w | (q,w) ∈ piece a} := by
  classical
  have hPrev : ∀ b ∈ P, fmt 6 H D {w | parent b = parent a ∧ (q,w) ∈ E b} := by
    intro b hb
    by_cases hp : parent b = parent a
    · exact fmt_congr (hE b (hP hb) q) (fun _ => by simp [hp])
    · have he : {w | parent b = parent a ∧ (q,w) ∈ E b} = ∅ := by ext w; simp [hp]
      rw [he]
      exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (fmt_empty 6 D) hH le_rfl
  have hUnion : fmt 6 ((P.card : ℝ) * H) D
      (⋃ b ∈ P, {w | parent b = parent a ∧ (q,w) ∈ E b}) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      fmt_biUnion P (fun _ => H) (fun b => {w | parent b = parent a ∧ (q,w) ∈ E b}) hPrev
  have hd : fmt 6 (H + (P.card : ℝ) * H) D
      ({w | (q,w) ∈ E a} \ ⋃ b ∈ P, {w | parent b = parent a ∧ (q,w) ∈ E b}) := by
    simpa only [max_self] using fmt_diff (hE a ha q) hUnion
  have ht : fmt 6 (H + (P.card : ℝ) * H) D {w | (q,w) ∈ piece a} := by
    apply fmt_congr hd
    intro w
    simp only [hrep, mem_sdiff, mem_iUnion, mem_ofPred_eq, selectedUnion]
  apply Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono ht _ le_rfl
  have hh : (P.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hP
  nlinarith [mul_le_mul_of_nonneg_right hh hH]

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
