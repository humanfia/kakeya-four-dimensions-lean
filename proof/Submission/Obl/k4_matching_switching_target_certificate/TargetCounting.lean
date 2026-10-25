import Mathlib

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- The finite collection of child labels above one coarse label. -/
def childFiber {α : Type*} (S : Set α) (F₀ F₁ : α → ℕ) (hF₁ : (F₁ '' S).Finite)
    (a : ℕ) : Finset ℕ :=
  (hF₁.subset (show F₁ '' {x | x ∈ S ∧ F₀ x = a} ⊆ F₁ '' S by
    rintro _ ⟨x, hx, rfl⟩; exact mem_image_of_mem _ hx.1)).toFinset

lemma mem_childFiber {α : Type*} {S : Set α} {F₀ F₁ : α → ℕ} (hF₁ : (F₁ '' S).Finite)
    {a d : ℕ} : d ∈ childFiber S F₀ F₁ hF₁ a ↔ ∃ x ∈ S, F₀ x = a ∧ F₁ x = d := by
  simp only [childFiber, Set.Finite.mem_toFinset, mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨hx, h₀⟩, h₁⟩
    exact ⟨x, hx, h₀, h₁⟩
  · rintro ⟨x, hx, h₀, h₁⟩
    exact ⟨x, ⟨hx, h₀⟩, h₁⟩

/-- All child labels above a finite set of coarse neighbors. -/
def childrenOver {α : Type*} (S : Set α) (F₀ F₁ : α → ℕ) (hF₁ : (F₁ '' S).Finite)
    (A : Finset ℕ) : Finset ℕ := A.biUnion (childFiber S F₀ F₁ hF₁)

lemma mem_childrenOver {α : Type*} {S : Set α} {F₀ F₁ : α → ℕ} (hF₁ : (F₁ '' S).Finite)
    {A : Finset ℕ} {d : ℕ} : d ∈ childrenOver S F₀ F₁ hF₁ A ↔
      ∃ x ∈ S, F₀ x ∈ A ∧ F₁ x = d := by
  simp only [childrenOver, Finset.mem_biUnion, mem_childFiber hF₁]
  constructor
  · rintro ⟨a, ha, x, hx, h₀, h₁⟩
    exact ⟨x, hx, h₀ ▸ ha, h₁⟩
  · rintro ⟨x, hx, h₀, h₁⟩
    exact ⟨F₀ x, h₀, x, hx, rfl, h₁⟩

theorem childrenOver_card_le {α : Type*} {S : Set α} {F₀ F₁ : α → ℕ}
    (hF₁ : (F₁ '' S).Finite) (A : Finset ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hdesc : ∀ x ∈ S, ((F₁ '' {y | y ∈ S ∧ F₀ y = F₀ x}).ncard : ℝ) ≤ B) :
    ((childrenOver S F₀ F₁ hF₁ A).card : ℝ) ≤ (A.card : ℝ) * B := by
  have hchild : ∀ a : ℕ, ((childFiber S F₀ F₁ hF₁ a).card : ℝ) ≤ B := by
    intro a
    by_cases hne : ∃ x ∈ S, F₀ x = a
    · obtain ⟨x, hx, hxa⟩ := hne
      have h := hdesc x hx
      rw [hxa] at h
      have hf : (F₁ '' {y | y ∈ S ∧ F₀ y = a}).Finite :=
        hF₁.subset (by rintro _ ⟨y, hy, rfl⟩; exact mem_image_of_mem _ hy.1)
      rw [Set.ncard_eq_toFinset_card _ hf] at h
      exact h
    · have hempty : childFiber S F₀ F₁ hF₁ a = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        obtain ⟨x, hx, hxa, _⟩ := mem_childFiber hF₁ |>.mp hd
        exact hne ⟨x, hx, hxa⟩
      simpa only [hempty, Finset.card_empty, Nat.cast_zero] using hB
  calc ((childrenOver S F₀ F₁ hF₁ A).card : ℝ)
      ≤ ((∑ a ∈ A, (childFiber S F₀ F₁ hF₁ a).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ a ∈ A, ((childFiber S F₀ F₁ hF₁ a).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ a ∈ A, B := Finset.sum_le_sum fun a _ => hchild a
    _ = (A.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

end Submission.Obl.k4_matching_switching_target_certificate
