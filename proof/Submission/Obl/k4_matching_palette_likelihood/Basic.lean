import Mathlib

open scoped BigOperators

namespace Submission.Obl.k4_matching_palette_likelihood

variable {α : Type*} [Fintype α]

noncomputable def fiberMass (p : α → ℝ) (f : α → ℕ) (b : ℕ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = b), p x

noncomputable def colorMass (p : α → ℝ) (f Z : α → ℕ) (b z : ℕ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = b ∧ Z x = z), p x

noncomputable def posterior (p : α → ℝ) (f Z : α → ℕ) (x : α) : ℝ :=
  colorMass p f Z (f x) (Z x) / fiberMass p f (f x)

noncomputable def entropy (p : α → ℝ) (f Z : α → ℕ) : ℝ :=
  -∑ x, p x * Real.log (posterior p f Z x)

lemma fiberMass_nonneg (p : α → ℝ) (f : α → ℕ) (hp : ∀ x, 0 ≤ p x) (b : ℕ) :
    0 ≤ fiberMass p f b := by
  exact Finset.sum_nonneg (fun x _ => hp x)

lemma colorMass_nonneg (p : α → ℝ) (f Z : α → ℕ) (hp : ∀ x, 0 ≤ p x) (b z : ℕ) :
    0 ≤ colorMass p f Z b z := by
  exact Finset.sum_nonneg (fun x _ => hp x)

lemma self_le_colorMass (p : α → ℝ) (f Z : α → ℕ) (hp : ∀ x, 0 ≤ p x) (x : α) :
    p x ≤ colorMass p f Z (f x) (Z x) := by
  classical
  exact Finset.single_le_sum (fun y _ => hp y) (by simp)

lemma colorMass_le_fiberMass (p : α → ℝ) (f Z : α → ℕ)
    (hp : ∀ x, 0 ≤ p x) (b z : ℕ) :
    colorMass p f Z b z ≤ fiberMass p f b := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; exact hx.1)
    (fun x _ _ => hp x)

lemma posterior_pos (p : α → ℝ) (f Z : α → ℕ) (hp : ∀ x, 0 ≤ p x)
    (x : α) (hx : 0 < p x) : 0 < posterior p f Z x := by
  have hA := lt_of_lt_of_le hx (self_le_colorMass p f Z hp x)
  exact div_pos hA (lt_of_lt_of_le hA (colorMass_le_fiberMass p f Z hp _ _))

lemma posterior_nonneg (p : α → ℝ) (f Z : α → ℕ) (hp : ∀ x, 0 ≤ p x)
    (x : α) : 0 ≤ posterior p f Z x :=
  div_nonneg (colorMass_nonneg p f Z hp _ _) (fiberMass_nonneg p f hp _)

lemma posterior_le_one (p : α → ℝ) (f Z : α → ℕ) (hp : ∀ x, 0 ≤ p x)
    (x : α) : posterior p f Z x ≤ 1 := by
  unfold posterior
  by_cases h : fiberMass p f (f x) = 0
  · simp [h]
  · exact (div_le_one (lt_of_le_of_ne (fiberMass_nonneg p f hp _) (Ne.symm h))).2
      (colorMass_le_fiberMass p f Z hp _ _)

lemma entropy_nonneg (p : α → ℝ) (f Z : α → ℕ) (hp : ∀ x, 0 ≤ p x) :
    0 ≤ entropy p f Z := by
  unfold entropy
  suffices (∑ x, p x * Real.log (posterior p f Z x)) ≤ 0 by linarith
  apply Finset.sum_nonpos
  intro x _
  by_cases hx : p x = 0
  · simp [hx]
  · exact mul_nonpos_of_nonneg_of_nonpos (hp x)
      (Real.log_nonpos (le_of_lt (posterior_pos p f Z hp x (lt_of_le_of_ne (hp x) (Ne.symm hx))))
        (posterior_le_one p f Z hp x))

end Submission.Obl.k4_matching_palette_likelihood
