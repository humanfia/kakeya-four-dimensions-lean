import Submission.Obl.k4_matching_palette_likelihood.Window
import Submission.Obl.k4_matching_palette_likelihood.Telescope

open scoped BigOperators

namespace Submission.Obl.k4_matching_palette_likelihood

lemma likelihood_of_entropy_bound {α : Type*} [Fintype α]
    (p : α → ℝ) (F : ℕ → α → ℕ) (Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hF : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (B : ℝ) (hB : ∀ k, entropy p (F k) Z ≤ B) (L C : ℕ) :
    (∑ a ∈ Finset.range L, ∑ x, p x *
      max 0 (Real.log (posterior p (F (a + C)) Z x / posterior p (F a) Z x))) ≤
        (C : ℝ) * B + (L : ℝ) := by
  calc
    _ ≤ ∑ a ∈ Finset.range L,
        (entropy p (F a) Z - entropy p (F (a + C)) Z + 1) := by
      apply Finset.sum_le_sum
      intro a _
      exact positive_log_window_le p (F a) (F (a + C)) Z hp hp1
        (fun x y hxy => nested_record F hF a (a + C) (Nat.le_add_right a C) x y hxy)
    _ = (∑ a ∈ Finset.range L, (entropy p (F a) Z - entropy p (F (a + C)) Z)) + L := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ (C : ℝ) * B + (L : ℝ) := by
      have h := sliding_potential_le (fun k => entropy p (F k) Z) B L C
        (fun k => entropy_nonneg p (F k) Z hp) hB
      linarith

lemma refined_palette_card {α : Type*} [Fintype α] (p : α → ℝ)
    (F : ℕ → α → ℕ) (Z : α → ℕ)
    (hF : ∀ k x y, F (k + 1) x = F (k + 1) y → F k x = F k y)
    (M : ℕ)
    (hM : ∀ x, ((Finset.univ.filter (fun y => 0 < p y ∧ F 0 y = F 0 x)).image Z).card ≤ M)
    (k : ℕ) (x : α) :
    ((Finset.univ.filter (fun y => 0 < p y ∧ F k y = F k x)).image Z).card ≤ M := by
  classical
  apply le_trans (Finset.card_le_card (Finset.image_subset_image _)) (hM x)
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact ⟨hy.1, nested_record F hF 0 k (Nat.zero_le k) y x hy.2⟩

end Submission.Obl.k4_matching_palette_likelihood
