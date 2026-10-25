import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.FiniteComparisonLists

/-! The finite comparison theorem with lists, as a named predicate of its
exponents, so that the exponents can be fixed before the final losses. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing

open Set MeasureTheory

/-- The conclusion of `Match3.finite_comparison_with_lists` at fixed exponents. -/
def ComparisonBound (d η R₀ : ℝ) : Prop :=
    ∀ (Ω Γ ι₁ ι₂ : Type) [MeasurableSpace Ω]
      [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
      [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [MeasurableSingletonClass ι₁] [MeasurableSingletonClass ι₂]
      (μ : Measure Ω) [IsFiniteMeasure μ] (s₁ : Finset ι₁) (s₂ : Finset ι₂)
      (E₁ : ι₁ → Set Ω) (E₂ : ι₂ → Set Ω)
      (domain₁ : ι₁ → Γ) (domain₂ : ι₂ → Γ) (reader : Ω → Γ)
      (T P Q X : Ω → ℝ) (h₁ : ι₁ → Fin 6 → ℝ) (h₂ : ι₂ → Fin 6 → ℝ)
      (t₀ p₀ q₀ V : Γ → ℝ) (τ D δ δm E A₀ A Mst : ℝ) (B : ENNReal),
      Measurable reader → Measurable T → Measurable P → Measurable Q →
      (∀ i, MeasurableSet (E₁ i)) → (∀ j, MeasurableSet (E₂ j)) →
      (∀ i ∈ s₁, E₁ i ⊆ {ω | reader ω = domain₁ i}) →
      (∀ j ∈ s₂, E₂ j ⊆ {ω | reader ω = domain₂ j}) →
      (∀ᵐ ω ∂μ, ∀ i ∈ s₁, ∀ j ∈ s₁, ω ∈ E₁ i → ω ∈ E₁ j → i = j) →
      (∀ᵐ ω ∂μ, ∀ i ∈ s₂, ∀ j ∈ s₂, ω ∈ E₂ i → ω ∈ E₂ j → i = j) →
      (∀ᵐ ω ∂μ, ∃ i ∈ s₁, ω ∈ E₁ i) → (∀ᵐ ω ∂μ, ∃ j ∈ s₂, ω ∈ E₂ j) →
      0 < τ → 0 < D → 0 < δ → δ ≤ 1 → 0 < δm → (∀ g, 0 < V g) → 1 ≤ E → 0 < A₀ →
      15360 * E * δm ≤ δ * τ → 15360 * E * δm ≤ δ * D →
      R₀ * δ ≤ Mst → 13720 ≤ A → 2000000 * A₀ * E ≤ A → A ≤ (Mst / δ) ^ η →
      (∀ g, ∀ᵐ ω ∂μ.restrict {ω | reader ω = g},
        T ω ∈ Icc (t₀ g) (t₀ g + τ) ∧ P ω ∈ Icc (p₀ g) (p₀ g + D) ∧
          Q ω ∈ Icc (q₀ g) (q₀ g + D)) →
      (∀ i ∈ s₁, ∀ ω ∈ E₁ i,
        |X ω - parameterPredictor (h₁ i) (T ω) (P ω) (Q ω)| ≤ δ / 2) →
      (∀ j ∈ s₂, ∀ ω ∈ E₂ j,
        |X ω - parameterPredictor (h₂ j) (T ω) (P ω) (Q ω)| ≤ δ / 2) →
      (∀ i ∈ s₁, ∀ t ∈ Icc (t₀ (domain₁ i)) (t₀ (domain₁ i) + τ),
        ∀ p ∈ Icc (p₀ (domain₁ i)) (p₀ (domain₁ i) + D),
        ∀ q ∈ Icc (q₀ (domain₁ i)) (q₀ (domain₁ i) + D),
          |parameterPredictor (h₁ i) t p q| ≤ E) →
      (∀ j ∈ s₂, ∀ t ∈ Icc (t₀ (domain₂ j)) (t₀ (domain₂ j) + τ),
        ∀ p ∈ Icc (p₀ (domain₂ j)) (p₀ (domain₂ j) + D),
        ∀ q ∈ Icc (q₀ (domain₂ j)) (q₀ (domain₂ j) + D),
          |parameterPredictor (h₂ j) t p q| ≤ E) →
      (∀ g σ, δ ≤ σ → σ ≤ 1 → ∀ (c : Fin 3 → ℤ) (j : ℤ),
        (μ.restrict {ω | reader ω = g})
          {ω | (fun k => ⌊(![T ω, P ω, Q ω] : Fin 3 → ℝ) k / δm⌋) = c ∧ ⌊X ω / σ⌋ = j} ≤
            ENNReal.ofReal (V g * σ ^ d * δm ^ 3)) →
      ((∑ i ∈ s₁, ENNReal.ofReal (τ * D ^ 2 * V (domain₁ i) * δ ^ d)) +
        (∑ j ∈ s₂, ENNReal.ofReal (τ * D ^ 2 * V (domain₂ j) * δ ^ d))) ≤ B →
      ENNReal.ofReal A₀⁻¹ * B < μ univ →
      ∃ ξ : Measure Ω, ξ ≤ μ ∧
        μ univ ≤ ξ univ +
          (ENNReal.ofReal A₀⁻¹ + ENNReal.ofReal (A * (Mst / δ) ^ (-η))) * B ∧
        ∃ L : ι₁ → Finset ι₂, (∀ i, L i ⊆ s₂) ∧
          (∀ i, ((L i).card : ℝ) ≤ 2000000 * A₀ * E * ((5120 * Mst) / δ) ^ d) ∧
          ∀ᵐ ω ∂ξ, ∃ i ∈ s₁, ∃ j ∈ s₂,
            ω ∈ E₁ i ∧ ω ∈ E₂ j ∧ domain₁ i = reader ω ∧ domain₂ j = reader ω ∧ j ∈ L i ∧
          ∀ t p q : ℝ, |t - (t₀ (reader ω) + τ / 2)| ≤ 4 * τ →
            |p - (p₀ (reader ω) + D / 2)| ≤ 4 * D →
            |q - (q₀ (reader ω) + D / 2)| ≤ 4 * D →
            |parameterPredictor (h₁ i) t p q - parameterPredictor (h₂ j) t p q| < 10 * Mst

theorem comparison_bound (hM : Matching) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ComparisonBound d η R₀ :=
  Match3.finite_comparison_with_lists hM hd0 hd1

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Pairing
