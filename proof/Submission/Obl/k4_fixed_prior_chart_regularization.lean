import Mathlib
import ChallengeDeps
import Submission.Obl.k4_fixed_prior_chart_regularization.Assembly
import Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope.Main
set_option linter.unusedVariables false

/-!
# Chart regularization under the original probability prior

Four measurable label restrictions supply local scalar counts, the row comparison,
the affine-slope comparison, and conditional dyadic coefficient-bin ceilings.
`Reg.chartRegularization_of_stages` chooses the intermediate losses backwards so
all four restrictions retain the final mass floor. The prior and the functions
`y`, `β`, `γ`, and `F` stay fixed throughout, including the full prior-bin mass
in each conditional ceiling. `Frozen` converts the resulting fields to the
frozen conjunction without strengthening any hypothesis.
-/

theorem Submission.k4_fixed_prior_chart_regularization : ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (Ω : Type) [MeasurableSpace Ω] (ν : MeasureTheory.Measure Ω), MeasureTheory.IsProbabilityMeasure ν → ∀ (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ), (Measurable y ∧ Measurable β ∧ Measurable γ ∧ Measurable F ∧ MeasurableSet E ∧ E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ l i, |y l i| ≤ N ^ η) ∧ (∀ l, |β l| ≤ N ^ η) ∧ (∀ l, |γ l| ≤ N ^ η) ∧ (∀ t i, |F t i| ≤ N ^ η) ∧ ENNReal.ofReal (N ^ η)⁻¹ ≤ (ν.prod MeasureTheory.volume) E ∧ (∀ t r w : ℝ, N ^ (-c) ≤ r → r ≤ 1 → N ^ (-c) ≤ w → w ≤ 1 → ∀ (z : Fin 2 → ℤ) (j : ℤ), ν {l | (l, t) ∈ E ∧ ⌊(β l + t * γ l) / w⌋ = j ∧ ⌊y l 0 / r⌋ = z 0 ∧ ⌊y l 1 / r⌋ = z 1} ≤ ENNReal.ofReal (N ^ η * r ^ 2 * w ^ d)) ∧ (∀ t w : ℝ, N ^ (-c) ≤ w → w ≤ 1 → ∃ C : Finset ℤ, (C.card : ℝ) ≤ N ^ η * w ^ (-d) ∧ ∀ l, (l, t) ∈ E → ⌊(β l + t * γ l - (F t 0 * y l 0 + F t 1 * y l 1)) / w⌋ ∈ C)) → ∃ E' : Set (Ω × ℝ), E' ⊆ E ∧ (Measurable y ∧ Measurable β ∧ Measurable γ ∧ Measurable F ∧ MeasurableSet E' ∧ E' ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ l i, |y l i| ≤ N ^ ε) ∧ (∀ l, |β l| ≤ N ^ ε) ∧ (∀ l, |γ l| ≤ N ^ ε) ∧ (∀ t i, |F t i| ≤ N ^ ε) ∧ ENNReal.ofReal (N ^ ε)⁻¹ ≤ (ν.prod MeasureTheory.volume) E' ∧ (∀ t q r a : ℝ, N ^ (-c) ≤ q → q ≤ r → r ≤ 1 → ∃ C : Finset ℤ, (C.card : ℝ) ≤ N ^ ε * (r / q) ^ d ∧ ∀ l, (l, t) ∈ E' → a ≤ β l + t * γ l - (F t 0 * y l 0 + F t 1 * y l 1) → β l + t * γ l - (F t 0 * y l 0 + F t 1 * y l 1) ≤ a + r → ⌊(β l + t * γ l - (F t 0 * y l 0 + F t 1 * y l 1)) / q⌋ ∈ C) ∧ (∀ t q : ℝ, N ^ (-c) ≤ q → q ≤ 1 → ∀ z : Fin 3 → ℤ, ν {l | (l, t) ∈ E' ∧ ⌊(β l + t * γ l) / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} ≤ ENNReal.ofReal (N ^ ε * q ^ (2 + d))) ∧ (∀ t u : ℝ, (∃ l, (l, t) ∈ E') → (∃ l, (l, u) ∈ E') → ∀ i, |F t i - F u i| ≤ N ^ ε * (|t - u| + N ^ (-c))) ∧ (∀ l l' t u, (l, t) ∈ E' → (l', u) ∈ E' → |γ l - γ l'| ≤ N ^ ε * (|t - u| + |β l + t * γ l - (β l' + u * γ l')| + |y l 0 - y l' 0| + |y l 1 - y l' 1| + N ^ (-c))) ∧ (∀ (q : ℝ) (n : ℕ), N ^ (-c) ≤ q → q ≤ (2 : ℝ) ^ (-(n : ℤ)) → ∀ (b : Fin 4 → ℤ) (t : ℝ) (z : Fin 3 → ℤ), ν {l | (⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧ ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3) ∧ (l, t) ∈ E' ∧ ⌊(β l + t * γ l) / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} ≤ ENNReal.ofReal (N ^ ε * (q / (2 : ℝ) ^ (-(n : ℤ))) ^ (2 + d)) * ν {l | ⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧ ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3})) := by
  exact Submission.Obl.k4_fixed_prior_chart_regularization.statement_of_stageSlope
    Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope.stageSlope
