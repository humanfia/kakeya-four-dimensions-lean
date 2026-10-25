import Mathlib

open scoped BigOperators

namespace Submission.Obl.k4_matching_palette_likelihood

/-- A bounded nonnegative potential controls the sum of all fixed-width increments. -/
lemma sliding_potential_le (H : ℕ → ℝ) (B : ℝ) (L C : ℕ)
    (h0 : ∀ a, 0 ≤ H a) (hB : ∀ a, H a ≤ B) :
    ∑ a ∈ Finset.range L, (H a - H (a + C)) ≤ (C : ℝ) * B := by
  have hid :
      (∑ a ∈ Finset.range L, H a) + (∑ a ∈ Finset.range C, H (a + L)) =
        (∑ a ∈ Finset.range C, H a) + (∑ a ∈ Finset.range L, H (a + C)) := by
    calc
      _ = ∑ a ∈ Finset.range (L + C), H a := by
        simpa only [Nat.add_comm] using (Finset.sum_range_add H L C).symm
      _ = _ := by simpa only [Nat.add_comm] using Finset.sum_range_add H C L
  have heq :
      (∑ a ∈ Finset.range L, (H a - H (a + C))) =
        ∑ a ∈ Finset.range C, (H a - H (a + L)) := by
    simp only [Finset.sum_sub_distrib]
    linarith
  rw [heq]
  calc
    _ ≤ ∑ a ∈ Finset.range C, B := Finset.sum_le_sum (fun a _ => by linarith [h0 (a + L), hB a])
    _ = (C : ℝ) * B := by simp

lemma nested_record {α : Type*} (F : ℕ → α → ℕ)
    (hF : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (a b : ℕ) (hab : a ≤ b) (x y : α) (hxy : F b x = F b y) : F a x = F a y := by
  induction b, hab using Nat.le_induction with
  | base => exact hxy
  | succ b hab ih => exact ih (hF b x y hxy)

end Submission.Obl.k4_matching_palette_likelihood
