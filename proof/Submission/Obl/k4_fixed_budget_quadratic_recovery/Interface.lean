/- Adapted within this LOT tree from o120/x0402, commit 81f800489248f55eaf1c2da13f86ceff0ee98719,
Submission/Obl/k4_unbounded_width_exclusion/Interface.lean. -/
import Mathlib
import ChallengeDeps

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

def fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  (fun n H D A => ∃ m₀ : ℕ, (m₀ : ℝ) ≤ H ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin n) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ A ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)

def ScalarMeshProjection : Prop :=
  (∀ d s m C S U ε : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (c : ℝ) (angular : Bool), (fun a : ℝ => (fun σ : ℝ => (fun y : α → ℝ → ℝ => (fun x : α → ℝ → ℝ => (fun z : α × ℝ → Fin 2 → ℤ => Measurable b → MeasureTheory.IsProbabilityMeasure ν → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ l i, |b l i| ≤ N ^ η) → N ^ (-C) ≤ c → c ≤ N ^ C → (∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s → μ {p | z p = q ∧ ⌊x p.1 p.2 / (N ^ (-r))⌋ = j} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * (N ^ (-r)) ^ d)) → (∃ F : Finset ((Fin 2 → ℤ) × ℤ), (F.card : ℝ) * σ ^ 2 ≤ N ^ η * c⁻¹ * a ^ (-d) ∧ ∀ᵐ p ∂μ, (z p, ⌊x p.1 p.2 / a⌋) ∈ F) → (angular = true → ∀ (r : ℝ) (q : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U → μ {p | z p = q ∧ ⌊x p.1 p.2 / a⌋ = j ∧ ⌊b p.1 1 / (N ^ (-r))⌋ = k} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * a ^ d * N ^ (-S * r))) → ∃ (n : ℕ) (β : ℝ) (A : Fin n → Set α) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), σ / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧ (angular = true → N ^ (-ε) ≤ β) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧ (∀ l ∈ A i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * a) ∧ ENNReal.ofReal (c * a ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | ∃ i, p.1 ∈ A i}) (fun p => ![⌊p.2 / σ⌋, ⌊y p.1 p.2 / σ⌋])) (fun l t => b l 2 + t * b l 3 + t ^ 2 * b l 4)) (fun l t => b l 0 + t * b l 1)) (N ^ (-m))) (N ^ (-s)))

end Submission.Obl.k4_fixed_budget_quadratic_recovery
