import Submission.Lib.K4FinitePlankAtlases.Basic

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Set
open scoped BigOperators

/-- A marked family with too much multiplicity contains a full-time heavy plank.
This is the finite stopping-rule consequence of the accepted weighted plank theorem. -/
theorem finite_plank_inverse (hweighted : WeightedPlankEstimate) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → Plane)
      (ω : Fin n → ℝ) (J : Fin n → Finset (Fin D)),
    (∀ i, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i, 0 < ω i) →
    (∀ i, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) →
    ∀ A : ℝ, 0 < A →
    C * A * (D : ℝ) ^ ε * ((visitedCells b u J).card : ℝ) <
      ∑ i, ω i * ((J i).card : ℝ) →
    ∃ (c w e₁ e₂ : Plane) (a β : ℝ),
      ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ inner ℝ e₁ e₂ = 0 ∧
      1 ≤ a ∧ a ≤ β ∧ β ≤ (D : ℝ) ∧ ∃ S : Finset (Fin n),
      (∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
        |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧
        |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) ∧
      A * a * β < ∑ i ∈ S, ω i := by
  intro ε hε
  obtain ⟨η, hη, C, hC, hbound⟩ := hweighted ε hε
  refine ⟨η, hη, C, hC, ?_⟩
  intro D hD n b u ω J hbu hω hmarks A hA hmult
  classical
  by_contra hnone
  have hcap : ∀ (c w e₁ e₂ : Plane) (a β : ℝ),
      ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 →
      1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset (Fin n),
      (∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
        |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧
        |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) →
      ∑ i ∈ S, ω i ≤ A * a * β := by
    intro c w e₁ e₂ a β he₁ he₂ he ha hab hβ S hS
    by_contra! hheavy
    exact hnone ⟨c, w, e₁, e₂, a, β, he₁, he₂, he, ha, hab, hβ, S, hS, hheavy⟩
  have hupper := hbound D hD n b u ω A J hbu hω hA hcap hmarks
  exact (not_le_of_gt hmult) (by
    simpa only [visitedCells, Submission.Lib.K4PlankGeometry.cellCode,
      Submission.Lib.K4PlankGeometry.binTime] using hupper)

end Submission.Lib.K4FinitePlankAtlases
