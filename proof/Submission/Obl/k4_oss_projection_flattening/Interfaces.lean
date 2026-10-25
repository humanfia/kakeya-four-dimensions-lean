import Mathlib
import ChallengeDeps

set_option linter.unusedVariables false

namespace Submission.Obl.k4_oss_projection_flattening

abbrev DenseRelationInput : Prop :=
  ∀ δ τ : ℝ, 0 < δ → 0 < τ → τ ≤ 1 → ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty → ∀ t : ℝ, t ∈ Set.Icc (1 / 4 : ℝ) 1 → (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') → (∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') → τ * (A.card : ℝ) ^ 2 * (B.card : ℝ) ≤ ((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ) → ∃ R : A → B → Prop, (τ / 10000) * (A.card : ℝ) * (B.card : ℝ) ≤ (Set.ncard {p : A × B | R p.1 p.2} : ℝ) ∧ ∃ (m : ℕ) (z : Fin m → ℝ), (m : ℝ) ≤ (10000 / τ) * (B.card : ℝ) ∧ ∀ (a : A) (b : B), R a b → ∃ i : Fin m, dist ((a : ℝ) + t * (b : ℝ)) (z i) ≤ δ

abbrev BadDirectionOutput : Prop :=
  ∀ b η : ℝ, 0 < b → b ≤ 1 → 0 < η → ∃ θ r : ℝ, 0 < θ ∧ θ ≤ η ∧ 0 < r ∧ r ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty → (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') → (∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') → (B.card : ℝ) ≤ δ ^ (-2 * θ) * (A.card : ℝ) → ∀ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-θ) * u ^ (b))) → ¬ (MeasureTheory.lintegral ν (fun t : ℝ => ENNReal.ofReal (((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ))) ≤ ENNReal.ofReal (δ ^ θ * (A.card : ℝ) ^ 2 * (B.card : ℝ))) → ∃ S : Finset ℝ, S.Nonempty ∧ (∀ t ∈ S, t ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ x u : ℝ, δ ≤ u → ((S.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-η) * u ^ b * (S.card : ℝ)) ∧ ∀ t ∈ S, ∃ R : A → B → Prop, δ ^ η * (A.card : ℝ) * (B.card : ℝ) ≤ (Set.ncard {p : A × B | R p.1 p.2} : ℝ) ∧ ∃ (m : ℕ) (z : Fin m → ℝ), (m : ℝ) < δ ^ (-η) * (A.card : ℝ) ∧ ∀ (a : A) (b : B), R a b → ∃ i : Fin m, dist ((a : ℝ) + t * (b : ℝ)) (z i) ≤ δ

abbrev FiniteEnergyGain (b g : ℝ) : Prop :=
  ∃ θ r : ℝ, 0 < θ ∧ 0 < r ∧ r ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < r → ∀ d : ℝ, 0 ≤ d → d ≤ 1 - (g) → ∀ A B : Finset ℝ, A.Nonempty → B.Nonempty → (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') → (∀ a ∈ B, ∀ a' ∈ B, a ≠ a' → δ ≤ dist a a') → (∀ x u : ℝ, δ ≤ u → ((A.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-θ) * u ^ (b) * (A.card : ℝ)) → (∀ x u : ℝ, δ ≤ u → ((B.filter (fun a => dist a x ≤ u)).card : ℝ) ≤ δ ^ (-θ) * u ^ (b) * (B.card : ℝ)) → δ ^ (θ - d) ≤ (A.card : ℝ) → (A.card : ℝ) ≤ δ ^ (-d - θ) → δ ^ (θ - d) ≤ (B.card : ℝ) → (B.card : ℝ) ≤ δ ^ (-d - θ) → ∀ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν → ν (Set.Icc (1 / 4 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, δ ≤ u → u ≤ 1 → ν (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-θ) * u ^ (b))) → MeasureTheory.lintegral ν (fun t : ℝ => ENNReal.ofReal (((((A.product B).product (A.product B)).filter (fun q : (ℝ × ℝ) × (ℝ × ℝ) => |q.1.1 + t * q.1.2 - (q.2.1 + t * q.2.2)| ≤ 16 * δ)).card : ℝ))) ≤ ENNReal.ofReal (δ ^ θ * (A.card : ℝ) ^ 2 * (B.card : ℝ))

end Submission.Obl.k4_oss_projection_flattening
