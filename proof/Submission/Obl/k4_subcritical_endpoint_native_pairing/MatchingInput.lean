/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Interface.lean.
   Original source attributions are retained below. -/
import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

def Matching : Prop := ((∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) → (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) → (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) → (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) → (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) → (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) → ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0))

end Submission.Obl.k4_subcritical_endpoint_native_pairing
