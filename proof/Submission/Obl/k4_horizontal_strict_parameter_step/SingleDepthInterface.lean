import Submission.Obl.k4_horizontal_strict_parameter_step.Interface

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/SingleDepthInterface.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Filter

/-- The full-time conclusion for one prescribed depth. -/
def LayersAt1 (N : ℕ → ℝ) (d e₀ u sMax : ℝ) {α : Type} [MeasurableSpace α]
    (ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s < sMax → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k in atTop, ∃ (σ : Measure (α × ℝ)), σ ≤ ρ k ∧
      ENNReal.ofReal (N k ^ (-ε)) ≤ σ Set.univ ∧
      ∃ (n : ℕ) (A : Fin n → Set α) (q : Fin n → Fin 3 → ℤ) (h : Fin n → Fin 6 → ℝ),
        LayerAt N d e₀ π b k ε σ (N k ^ (-u * s)) (N k ^ (-s)) n A q h

/-- The same universal prepared-input engine, with only one requested depth. -/
def EngineAt1 (d κ ℓ S U e₀ u sMax : ℝ) : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop →
    ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) →
    ∀ (α : Type) [MeasurableSpace α] (ν : ℕ → Measure α) (μ ρ : ℕ → Measure (α × ℝ))
      (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ)
      (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α) (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ),
      Hyp1 K ν μ ρ π b P → Hyp2 N K d S μ π b P → Hyp3 N K d κ ℓ U e₀ ν μ π b P T n j A B c F →
      Hyp4 U T n j A → LayersAt1 N d e₀ u sMax ρ π b


end Submission.Obl.k4_horizontal_strict_parameter_step
