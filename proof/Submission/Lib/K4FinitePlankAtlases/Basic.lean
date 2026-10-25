import Mathlib
import Submission.Lib.K4PlankGeometry

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Set
open scoped BigOperators

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The finite weighted plank estimate supplied by the caller. -/
def WeightedPlankEstimate : Prop := ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → EuclideanSpace ℝ (Fin 2)) (ω : Fin n → ℝ) (A : ℝ) (J : Fin n → Finset (Fin D)), (∀ i : Fin n, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i : Fin n, 0 < ω i) → 0 < A → (∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ), ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset (Fin n), (∀ i ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧ |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) → ∑ i ∈ S, ω i ≤ A * a * β) → (∀ i : Fin n, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) → ∑ i : Fin n, ω i * ((J i).card : ℝ) ≤ C * A * (D : ℝ) ^ ε * ((((Finset.univ : Finset (Fin n)).sigma J).image (fun p => ((p.2 : ℕ), fun k : Fin 2 => ⌊(D : ℝ) * (b p.1 + (((((p.2 : ℕ) : ℝ) + 1 / 2) / (D : ℝ)) • u p.1)) k⌋))).card : ℝ)

/-- The actual visited time-position cells, including all original trajectory tags. -/
noncomputable def visitedCells {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b u : ι → Plane) (J : ι → Finset (Fin D)) : Finset (ℕ × (Fin 2 → ℤ)) :=
  ((Finset.univ : Finset ι).sigma J).image
    (fun p => Submission.Lib.K4PlankGeometry.cellCode D (b p.1) (u p.1) p.2)


end Submission.Lib.K4FinitePlankAtlases
