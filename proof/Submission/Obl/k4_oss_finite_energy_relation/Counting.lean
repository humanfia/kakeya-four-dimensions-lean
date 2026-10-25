import Mathlib

namespace Submission.Obl.k4_oss_finite_energy_relation

open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem card_product_filter_eq_sum {α β : Type*} (S : Finset α) (T : Finset β)
    (r : α → β → Prop) :
    (((S.product T).filter (fun p : α × β => r p.1 p.2)).card : ℝ) =
      ∑ a ∈ S, ((T.filter (r a)).card : ℝ) := by
  classical
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.product_eq_sprod, Finset.sum_product]

/-- Discarding terms below a threshold loses at most threshold times cardinality. -/
theorem sum_le_threshold_add_popular {α : Type*} (S : Finset α) (w : α → ℝ)
    {L M : ℝ} (hL : 0 ≤ L) (hw : ∀ a ∈ S, w a ≤ M) :
    (∑ a ∈ S, w a) ≤ L * S.card + M * (S.filter (fun a => L ≤ w a)).card := by
  classical
  calc
    (∑ a ∈ S, w a) ≤ ∑ a ∈ S, (L + if L ≤ w a then M else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs with h
      · linarith [hw a ha]
      · linarith
    _ = L * S.card + M * (S.filter (fun a => L ≤ w a)).card := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [mul_comm]

end Submission.Obl.k4_oss_finite_energy_relation
