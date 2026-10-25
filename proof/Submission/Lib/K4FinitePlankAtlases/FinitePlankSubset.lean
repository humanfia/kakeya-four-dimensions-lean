import Submission.Lib.K4FinitePlankAtlases.FinitePlankInverse

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Set
open scoped BigOperators

/-- The cap seen by a residual set of trajectory indices. -/
def ResidualPlankCap {D : ℕ} {ι : Type*} [DecidableEq ι]
    (b u : ι → Plane) (ω : ι → ℝ) (A : ℝ) (R : Finset ι) : Prop :=
  ∀ (c w e₁ e₂ : Plane) (a β : ℝ),
    ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 →
    1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset ι, S ⊆ R →
    (∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧
      |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) →
    ∑ i ∈ S, ω i ≤ A * a * β

/-- The weighted estimate applies to residual indices with their original positive
weights; discarded indices need not be assigned zero weights in its hypotheses. -/
theorem weighted_plank_subset (hweighted : WeightedPlankEstimate) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (D : ℕ), 1 ≤ D → ∀ (ι : Type*) [Fintype ι] [DecidableEq ι]
      (b u : ι → Plane) (ω : ι → ℝ) (J : ι → Finset (Fin D)),
    (∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i, 0 < ω i) →
    (∀ i, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) →
    ∀ (A : ℝ) (R : Finset ι), 0 < A → ResidualPlankCap (D := D) b u ω A R →
      ∑ i ∈ R, ω i * ((J i).card : ℝ) ≤
        C * A * (D : ℝ) ^ ε * ((visitedCells b u J).card : ℝ) := by
  intro ε hε
  obtain ⟨η, hη, C, hC, hbound⟩ := hweighted ε hε
  refine ⟨η, hη, C, hC, ?_⟩
  intro D hD ι hι hdec b u ω J hbu hω hmarks A R hA hcap
  classical
  let e : R ≃ Fin R.card := R.equivFin
  let rep : Fin R.card → ι := fun j => (e.symm j).val
  have hrep (j : Fin R.card) : rep j ∈ R := (e.symm j).property
  have hinj : Function.Injective rep := by
    intro i j h
    exact e.symm.injective (Subtype.ext h)
  have hcap' : ∀ (c w e₁ e₂ : Plane) (a β : ℝ),
      ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 →
      1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset (Fin R.card),
      (∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
        |inner ℝ (b (rep i) + t • u (rep i) - c - t • w) e₁| ≤ a / (D : ℝ) ∧
        |inner ℝ (b (rep i) + t • u (rep i) - c - t • w) e₂| ≤ β / (D : ℝ)) →
      ∑ i ∈ S, ω (rep i) ≤ A * a * β := by
    intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ S hS
    have hsub : S.image rep ⊆ R := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact hrep j
    have hfit : ∀ i ∈ S.image rep, ∀ t ∈ Icc (0 : ℝ) 1,
        |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧
        |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ) := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact hS j hj
    have h := hcap c w e₁ e₂ a β he₁ he₂ he ha hab hβ (S.image rep) hsub hfit
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)] at h
    exact h
  have h := hbound D hD R.card (b ∘ rep) (u ∘ rep) (ω ∘ rep) A (J ∘ rep)
    (fun j => hbu _) (fun j => hω _) hA hcap' (fun j => hmarks _)
  have hmass : (∑ j : Fin R.card, ω (rep j) * ((J (rep j)).card : ℝ)) =
      ∑ i ∈ R, ω i * ((J i).card : ℝ) := by
    calc
      _ = ∑ j : R, ω j * ((J j).card : ℝ) :=
        e.symm.sum_comp (fun j : R => ω j * ((J j).card : ℝ))
      _ = _ := by
        change (∑ j ∈ R.attach, ω j.val * ((J j.val).card : ℝ)) = _
        exact Finset.sum_attach R (fun j => ω j * ((J j).card : ℝ))
  have hsub : visitedCells (b ∘ rep) (u ∘ rep) (J ∘ rep) ⊆ visitedCells b u J := by
    intro x hx
    obtain ⟨⟨j, k⟩, hj, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨⟨rep j, k⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, (Finset.mem_sigma.mp hj).2⟩
  have hbound' : (∑ j : Fin R.card, ω (rep j) * ((J (rep j)).card : ℝ)) ≤
      C * A * (D : ℝ) ^ ε * ((visitedCells (b ∘ rep) (u ∘ rep) (J ∘ rep)).card : ℝ) := by
    simpa only [visitedCells, Submission.Lib.K4PlankGeometry.cellCode,
      Submission.Lib.K4PlankGeometry.binTime, Function.comp_apply] using h
  rw [hmass] at hbound'
  apply hbound'.trans
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast Finset.card_le_card hsub
  · positivity

end Submission.Lib.K4FinitePlankAtlases
