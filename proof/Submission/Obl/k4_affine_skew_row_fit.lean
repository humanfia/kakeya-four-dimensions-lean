import Mathlib
import ChallengeDeps
import Submission.Obl.k4_affine_skew_row_fit.FrozenPacking
import Submission.Obl.k4_affine_skew_row_fit.Assembly
import Submission.Obl.k4_affine_skew_row_fit.Expanded
set_option linter.unusedVariables false

/-!
# `Submission.k4_affine_skew_row_fit`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_affine_skew_row_fit`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_affine_skew_row_fit/`
belong to this obligation.
-/

theorem Submission.k4_affine_skew_row_fit : (∀ s : ℝ, 0 < s → s ≤ 1 → ∃ n : ℕ, 2 ≤ n ∧ ∃ r₀ ε₀ τ : ℝ, 0 < r₀ ∧ 0 < ε₀ ∧ 0 < τ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ → μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, r ≤ u → u ≤ 1 → μ (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε₀) * u ^ s)) → ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ → ‖MeasureTheory.integral (MeasureTheory.Measure.pi (fun _ : Fin n => μ)) (fun x : Fin n → ℝ => Complex.exp (((-2 * Real.pi * ξ * (∏ j : Fin n, x j) : ℝ) : ℂ) * Complex.I))‖ ≤ |ξ| ^ (-τ)) → (∀ S a ε : ℝ, 0 < S → 0 < a → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b v H : α → ℝ) (T : α × ℝ → Fin 2 → ℝ) (π : MeasureTheory.Measure ℝ) (E : ℝ) (F : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)), (fun ξ : ℝ => (fun z : α × ℝ → Fin 2 → ℝ => (fun q : α × ℝ → Fin 2 → ℤ => Measurable b → Measurable v → Measurable H → Measurable T → MeasureTheory.IsProbabilityMeasure ν → MeasureTheory.IsProbabilityMeasure π → ξ ≤ E → E ≤ 1 → (∀ l, |b l| + |v l| ≤ N ^ η) → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ x r : ℝ, ξ ≤ r → r ≤ 1 → π (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) → (∀ (p₀ : Fin 2 → ℤ) (j : ℤ), μ {p | q p = p₀ ∧ ⌊v p.1 / ξ⌋ = j} ≤ ENNReal.ofReal (N ^ η * ξ ^ 2) * π (Set.Ico ((j : ℝ) * ξ) (((j : ℝ) + 1) * ξ))) → (∀ p₀, ((F p₀).card : ℝ) ≤ N ^ η) → (∀ᵐ p ∂μ, (∀ j, |T p j| ≤ N ^ η) ∧ (fun j => ⌊T p j / E⌋) ∈ F (q p) ∧ |T p 0 + v p.1 * T p 1 - H p.1| ≤ N ^ η * E) → ∃ (B : Fin 2 → ℝ) (ℓ : ℝ), |B 0| + |B 1| + |ℓ| ≤ N ^ ε ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | |T p 0 - B 0 + ℓ * z p 1| ≤ N ^ ε * E ∧ |T p 1 - B 1 - ℓ * z p 0| ≤ N ^ ε * E}) (fun p j => ⌊z p j / ξ⌋)) (fun p => ![p.2, b p.1 + p.2 * v p.1])) (N ^ (-a))) := by
  intro hdecay
  exact Submission.Obl.k4_affine_skew_row_fit.expanded_of_uniform
    (Submission.Obl.k4_affine_skew_row_fit.uniform_row_fit_of_graphs
      Submission.Obl.k4_affine_skew_row_fit.graph_reduction_of_frozen
      (Submission.Obl.k4_affine_skew_row_fit.planar_rigidity_of_frozen hdecay))
