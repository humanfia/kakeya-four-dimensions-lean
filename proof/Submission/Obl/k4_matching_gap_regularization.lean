import Mathlib
import ChallengeDeps
import Submission.Obl.k4_matching_gap_regularization.Finish
set_option linter.unusedVariables false

/-!
# `Submission.k4_matching_gap_regularization`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_matching_gap_regularization`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_matching_gap_regularization/`
belong to this obligation.
-/

theorem Submission.k4_matching_gap_regularization : ∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → (fun Bad : ℝ → ℝ → Prop => (∃ N : ℕ → ℝ, ∀ k : ℕ, (k : ℝ) + 2 ≤ N k ∧ Bad (1 / ((k : ℝ) + 1)) (N k)) → ∃ β : ℕ → ℝ, ((∀ j : ℕ, 1 ≤ j → j ≤ J → 0 ≤ β j ∧ β j ≤ 2) ∧ (∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ β j = 0)) ∧ (fun Gap : ℝ → ℝ → Prop => (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ Gap ε N)) (fun (ε N : ℝ) => ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + ε) ∧ (n₂ : ℝ) ≤ N ^ (d + ε) ∧ (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ ε) ∧ (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ ε) ∧ (∀ i : Fin n₁, 0 ≤ π₁ i) ∧ (∀ i : Fin n₂, 0 ≤ π₂ i) ∧ (∑ i : Fin n₁, π₁ i) = 1 ∧ (∑ i : Fin n₂, π₂ i) = 1 ∧ MeasureTheory.IsProbabilityMeasure μ ∧ (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₁ i) * MeasureTheory.volume E) ∧ (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ ε * π₂ i) * MeasureTheory.volume E) ∧ μ {p | p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + ε) ∧ ∀ j : ℕ, 1 ≤ j → j ≤ J → |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| ≤ N ^ (-β j + ε) ∧ (β j < 2 → N ^ (-β j - ε) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|)}ᶜ = 0)) (fun (η N : ℝ) => ∃ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) ∧ (n₂ : ℝ) ≤ N ^ (d + η) ∧ (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) ∧ (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) ∧ (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) ∧ (∀ i : Fin n₁, 0 ≤ π₁ i) ∧ (∀ i : Fin n₂, 0 ≤ π₂ i) ∧ (∑ i : Fin n₁, π₁ i) = 1 ∧ (∑ i : Fin n₂, π₂ i) = 1 ∧ MeasureTheory.IsProbabilityMeasure μ ∧ (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) ∧ (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) ∧ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0) := by
  intro D J hD hDJ d hd
  simpa only [Submission.Obl.k4_matching_gap_regularization.Bad,
    Submission.Obl.k4_matching_gap_regularization.Gap,
    Submission.Obl.k4_matching_gap_regularization.Base,
    Submission.Obl.k4_matching_gap_regularization.BadSet,
    Submission.Obl.k4_matching_gap_regularization.GapSet,
    Submission.Obl.k4_matching_gap_regularization.Admissible, and_assoc] using
    (Submission.Obl.k4_matching_gap_regularization.fixed_exponents
      (D := D) (J := J) (d := d) hDJ.le)
