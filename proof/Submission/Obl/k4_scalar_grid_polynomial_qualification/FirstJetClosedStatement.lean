import Mathlib
import ChallengeDeps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

/-- Closed Mathlib-only first-jet interface. No tree recursion or
higher-degree polynomial fitting is assumed in this assertion. -/
def FirstJetInput : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∀ (r : ℕ) (γ : Fin r → ℝ) (γ₀ : ℝ), (∀ i, 0 < γ i) →
    (∀ i, γ i ≤ γ₀) → 0 < γ₀ → ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ (Λ : Type) [MeasurableSpace Λ] (ν : MeasureTheory.Measure Λ) (c : Λ → Fin 5 → ℝ) (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (piece : ℝ → Λ → Fin 5 → ℤ) (K ζ : ℝ) (Tl : Fin r → ℕ) (T₀ : ℕ), (fun (zx : (Fin 5 → ℝ) → ℝ → ℝ) => (fun (zy : (Fin 5 → ℝ) → ℝ → ℝ) => (fun (scalar : (Fin 5 → ℝ) → ℝ → ℝ) => (fun (resid : (Fin 5 → ℝ) → ℝ → ℝ) => (fun (pos : (Fin 5 → ℝ) → ℝ → Fin 3 → ℝ) => (fun (h : ℝ) => K ≤ N ^ α → ζ ≤ N ^ (-cζ) → (∀ i, N ^ (-γ i) / K ≤ ((2 : ℝ) ^ Tl i)⁻¹ ∧ ((2 : ℝ) ^ Tl i)⁻¹ ≤ K * N ^ (-γ i)) → N ^ (-γ₀) / K ≤ h → h ≤ K * N ^ (-γ₀) → (∀ i, Tl i ≤ T₀) → MeasureTheory.IsProbabilityMeasure ν → 1 ≤ K → 0 < ζ → ζ ≤ 1 → Measurable c → MeasurableSet E → Measurable F → (∀ r, Measurable (piece r)) → (∀ p ∈ E, p.2 ∈ Set.Icc (0 : ℝ) 1) → (∀ p ∈ E, ∀ e, |c p.1 e| ≤ K) → (∀ p ∈ E, |F p.2| ≤ K) → ENNReal.ofReal K⁻¹ ≤ (ν.prod MeasureTheory.volume) E → (∀ t r R a : ℝ, ζ ≤ r → r ≤ R → ∃ (m : ℕ) (z : Fin m → ℝ), {s : ℝ | ∃ l, (l,t) ∈ E ∧ scalar (c l) t = s} ∩ Set.Icc a (a + R) ⊆ ⋃ i, Metric.closedBall (z i) r ∧ (m : ℝ) ≤ K * (R / r) ^ d) → (∀ t a b q : ℝ, ζ ≤ q → q ≤ 1 → ν {l | (l,t) ∈ E ∧ zx (c l) t ∈ Set.Ico a (a + q) ∧ zy (c l) t ∈ Set.Ico b (b + q)} ≤ ENNReal.ofReal (K * q ^ (1 + d))) → (∀ p ∈ E, ∀ p' ∈ E, |F p.2 - F p'.2| ≤ K * (|p.2 - p'.2| + ζ)) → (∀ p ∈ E, ∀ p' ∈ E, |resid (c p.1) p.2 - resid (c p'.1) p'.2| ≤ K * (‖pos (c p.1) p.2 - pos (c p'.1) p'.2‖ + ζ)) → (∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∀ l l', piece r l = piece r l' → ‖c l - c l'‖ ≤ r) → (∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∀ (b : Fin 5 → ℤ) (t a a' q : ℝ), ζ ≤ q → q ≤ r → ν {l | piece r l = b ∧ (l,t) ∈ E ∧ zx (c l) t ∈ Set.Ico a (a + q) ∧ zy (c l) t ∈ Set.Ico a' (a' + q)} ≤ ENNReal.ofReal (K * (q / r) ^ (1 + d)) * ν {l | piece r l = b}) → ∃ E₁ : Set (Λ × ℝ), E₁ ⊆ E ∧ MeasurableSet E₁ ∧
  ENNReal.ofReal (N ^ (-ε)) ≤ (ν.prod MeasureTheory.volume) E₁ ∧
  ∃ A : ℝ → ℝ, Measurable A ∧ (∀ p ∈ E₁, |A p.2| ≤ N ^ ε) ∧
    (∀ i (j : ℤ), ∀ p ∈ E₁, ∀ p' ∈ E₁,
      p.2 ∈ Set.Ico ((j : ℝ) / (2 : ℝ) ^ Tl i) (((j : ℝ) + 1) / (2 : ℝ) ^ Tl i) →
      p'.2 ∈ Set.Ico ((j : ℝ) / (2 : ℝ) ^ Tl i) (((j : ℝ) + 1) / (2 : ℝ) ^ Tl i) →
      |F p'.2 - F p.2 - (p'.2 - p.2) * A p.2| ≤
        N ^ ε * (((2 : ℝ) ^ Tl i)⁻¹) ^ ((11 : ℝ) / 10)) ∧
    ∀ t : ℝ, ∃ Y : ℤ → Finset ℝ, (∀ σ, (Y σ).card ≤ ⌊N ^ ε⌋₊) ∧
      ∀ l ∈ Set.univ, (l,t) ∈ E₁ → ∃ v ∈ Y ⌊scalar (c l) t / h⌋,
        |c l 1 + 2 * c l 2 * t - A t * zy (c l) t - F t * c l 4 - v| ≤
          N ^ ε * h ^ ((1 - d) / 32)) (((2 : ℝ) ^ T₀)⁻¹)) (fun a t => ![t, zx a t, zy a t])) (fun a t => a 1 + 2 * a 2 * t - F t * a 4)) (fun a t => zx a t - F t * zy a t)) (fun a t => a 3 + a 4 * t)) (fun a t => a 0 + a 1 * t + a 2 * t ^ 2)

end Submission.Obl.k4_scalar_grid_polynomial_qualification
