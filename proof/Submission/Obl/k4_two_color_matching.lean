import Mathlib
import ChallengeDeps
import Submission.Obl.k4_matching_palette_likelihood
import Submission.Obl.k4_matching_endpoint_volume
import Submission.Obl.k4_matching_refinement_exponent
import Submission.Obl.k4_two_color_matching.JetScales
import Submission.Obl.k4_two_color_matching.LocalInjectivity
import Submission.Obl.k4_two_color_matching.LossReduction
import Submission.Obl.k4_two_color_matching.Configuration
import Submission.Obl.k4_two_color_matching.Endpoint

set_option linter.unusedVariables false

/-!
# Two-color matching from palette likelihood and endpoint volume

The children contain the probabilistic and analytic refinements argument.
This glue only passes from the canonical vanishing-loss counterexample
sequence to one fixed positive input tolerance.
-/

theorem Submission.k4_two_color_matching : ∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) → (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) → (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) → (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) → (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) → (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) → ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0 := by
  classical
  intro D J hD hDJ d hd hdlt
  let Bad : ℝ → ℝ → Prop := fun (η N : ℝ) => ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)),
    (n₁ : ℝ) ≤ N ^ (d + η) ∧ (n₂ : ℝ) ≤ N ^ (d + η) ∧
    (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧
    (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧
    (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) ∧
    (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) ∧
    (∀ i : Fin n₁, 0 ≤ π₁ i) ∧ (∀ i : Fin n₂, 0 ≤ π₂ i) ∧
    (∑ i : Fin n₁, π₁ i) = 1 ∧ (∑ i : Fin n₂, π₂ i) = 1 ∧
    MeasureTheory.IsProbabilityMeasure μ ∧
    (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) ∧
    (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) ∧
    μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0
  have hseq : ¬ ∃ N : ℕ → ℝ, ∀ k : ℕ,
      (k : ℝ) + 2 ≤ N k ∧
        Bad (Submission.Obl.k4_two_color_matching.lossExponent k) (N k) := by
    intro h
    have hlower : 1 ≤ d :=
      Submission.k4_matching_refinement_exponent
        Submission.k4_matching_palette_likelihood
        Submission.k4_matching_endpoint_volume D J hD hDJ d hd h
    exact (not_le_of_gt hdlt) hlower
  obtain ⟨η, hη, N₀, hN₀, hgood⟩ :=
    Submission.Obl.k4_two_color_matching.uniform_of_no_counterexample_sequence Bad hseq
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN n₁ n₂ f₁ f₂ π₁ π₂ μ hn₁ hn₂ hf₁ hf₂ hder₁ hder₂
    hπ₁ hπ₂ hsum₁ hsum₂ hμ hm₁ hm₂ hsupport
  exact hgood N hN ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, hn₁, hn₂,
    hf₁, hf₂, hder₁, hder₂, hπ₁, hπ₂, hsum₁, hsum₂, hμ, hm₁, hm₂, hsupport⟩
