import Mathlib
import ChallengeDeps
import Submission.Obl.k4_retained_edge_planar_rigidity.Main
set_option linter.unusedVariables false

/-!
# `Submission.k4_retained_edge_planar_rigidity`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_retained_edge_planar_rigidity`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_retained_edge_planar_rigidity/`
belong to this obligation.
-/

theorem Submission.k4_retained_edge_planar_rigidity : (∀ s : ℝ, 0 < s → s ≤ 1 → ∃ n : ℕ, 2 ≤ n ∧ ∃ r₀ ε₀ τ : ℝ, 0 < r₀ ∧ 0 < ε₀ ∧ 0 < τ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ → μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, r ≤ u → u ≤ 1 → μ (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε₀) * u ^ s)) → ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ → ‖MeasureTheory.integral (MeasureTheory.Measure.pi (fun _ : Fin n => μ)) (fun x : Fin n → ℝ => Complex.exp (((-2 * Real.pi * ξ * (∏ j : Fin n, x j) : ℝ) : ℂ) * Complex.I))‖ ≤ |ξ| ^ (-τ)) → ∀ S : ℝ, 0 < S → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ → (fun K : ℝ => ∀ (m : ℕ) (w κ : Fin m → ℝ) (A B : Finset (ℝ × ℝ)) (G : Fin m → Finset ((ℝ × ℝ) × (ℝ × ℝ))), (∀ x ∈ A, ∃ a b : ℤ, x = (h * a, h * b)) → (∀ y ∈ B, ∃ a b : ℤ, y = (h * a, h * b)) → (∀ x ∈ A, |x.1| ≤ K ∧ |x.2| ≤ K) → (∀ y ∈ B, |y.1| ≤ K ∧ |y.2| ≤ K) → (1 / (K * h) ≤ (A.card : ℝ)) → ((A.card : ℝ) ≤ K / h) → (1 / (K * h) ≤ (B.card : ℝ)) → ((B.card : ℝ) ≤ K / h) → (∀ i : Fin m, 0 ≤ w i) → ((∑ i : Fin m, w i) = 1) → (∀ i : Fin m, 1 / K ≤ |κ i| ∧ |κ i| ≤ K) → (∀ x r : ℝ, h ≤ r → r ≤ 1 → (∑ i : Fin m, if κ i ∈ Set.Icc x (x + r) then w i else 0) ≤ K * r ^ S) → (∀ i : Fin m, G i ⊆ A ×ˢ B) → (∀ i : Fin m, 1 / (K * h ^ 2) ≤ ((G i).card : ℝ)) → (∀ i : Fin m, (((G i).image (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => (⌊(p.1.1 + κ i * p.2.1) / h⌋, ⌊(p.1.2 + κ i * p.2.2) / h⌋))).card : ℝ) ≤ K / h) → (∀ (i : Fin m) (x y : ℝ), (((G i).filter (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => p.1.1 ∈ Set.Ico x (x + h) ∧ p.2.1 ∈ Set.Ico y (y + h))).card : ℝ) ≤ K * h ^ 2 * ((G i).card : ℝ)) → ∃ i : Fin m, ∃ G' : Finset ((ℝ × ℝ) × (ℝ × ℝ)), G' ⊆ G i ∧ h ^ ε / h ^ 2 ≤ (G'.card : ℝ) ∧ ∃ ℓ c₁ c₂ : ℝ, |ℓ| + |c₁| + |c₂| ≤ h ^ (-ε) ∧ ∀ p ∈ G', |p.1.2 - ℓ * p.1.1 - c₁| + |p.2.2 - ℓ * p.2.1 - c₂| ≤ h ^ (1 - ε)) (h ^ (-η)) :=
  Submission.Obl.k4_retained_edge_planar_rigidity.main
