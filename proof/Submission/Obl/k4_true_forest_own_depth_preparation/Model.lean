import Submission.Obl.k4_coarsened_outer_horizon_composition.Interface

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set
open Submission.Obl.k4_coarsened_outer_horizon_composition

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Inc := Line × ℝ
abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev Obs := EuclideanSpace ℝ (Fin 3) × ℤ

/-- The unchanged finite true-forest predicate in the frozen statement. -/
def Core (N K : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (M D k m : ℕ) (r : ℕ → ℝ) (T : ℕ → ℕ) (κ : ℝ) (C : ℕ)
    (lev : Fin C → ℕ) (par : Fin C → Fin C) (γ : Fin C → Fin (W k))
    (j : Fin C → ℕ) (c u : Fin C → E2)
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ)
    (A : Fin C → Set Line) (F : Fin C → Set Inc) : Prop :=
  1 ≤ κ ∧ K k ≤ κ ∧ (C : ℝ) ≤ N k ^ M ∧
  (∀ i, i < m → ENNReal.ofReal κ⁻¹ ≤ ∑ b, if lev b = i then
    ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod volume) (F b) else 0) ∧
  (∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' →
    Disjoint (A b) (A b')) ∧
  ∀ b, lev b < m ∧ j b < 2 ^ T (lev b) ∧
    chart (N k) M D κ (T (lev b)) (j b : ℝ) (r (lev b))
      (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b)
      (ENNReal.ofReal (N k ^ (-f (r (lev b))) * |Matrix.det (Q b)| /
        ((2 : ℝ) ^ T (lev b) * κ)) ≤ ((ν k (γ b)).prod volume) (F b)) ∧
    (0 < lev b → lev (par b) + 1 = lev b ∧ γ (par b) = γ b ∧
      A b ⊆ A (par b) ∧ F b ⊆ F (par b) ∧
      (j (par b) : ℝ) / (2 : ℝ) ^ T (lev (par b)) ≤
        (j b : ℝ) / (2 : ℝ) ^ T (lev b) ∧
      ((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b) ≤
        ((j (par b) : ℝ) + 1) / (2 : ℝ) ^ T (lev (par b)))

/-- The preparation assertion, with the frozen predicates given names. -/
def Preparation : Prop :=
  ∀ N K L d S η W ω ν E P B f g G,
    prob N K L d S η W ω ν E P B f g G →
    ∀ (m : ℕ) (r : ℕ → ℝ), 0 < m →
    (∀ i, i < m → 0 < r i ∧ r i ≤ L) → ∀ M D : ℕ,
    ∃ M' D' : ℕ, M ≤ M' ∧ D ≤ D' ∧ ∀ σ : ℝ, 0 < σ →
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ σ ∧ ∀ᶠ k in Filter.atTop,
    ∀ (T : ℕ → ℕ) (C : ℕ) (lev : Fin C → ℕ) (par : Fin C → Fin C)
      (γ : Fin C → Fin (W k)) (j : Fin C → ℕ) (c u : Fin C → E2)
      (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
      (R : Fin C → MvPolynomial (Fin 4) ℝ)
      (A : Fin C → Set Line) (F : Fin C → Set Inc),
    (∀ i, i < m → (2 : ℝ) ^ T i ≤ N k ^ M) →
    Core N K W ω ν E B f M D k m r T (N k ^ ρ) C lev par γ j c u Q R A F →
    ∃ (C' : ℕ) (emb : Fin C' ↪ Fin C) (par' : Fin C' → Fin C')
      (F' : Fin C' → Set Inc) (lst : ℕ → Fin (W k) → Obs → Finset (Fin C')),
    C' ≤ C ∧
    Core N K W ω ν E B f M' D' k m r T (N k ^ σ) C'
      (fun b => lev (emb b)) par' (fun b => γ (emb b)) (fun b => j (emb b))
      (fun b => c (emb b)) (fun b => u (emb b)) (fun b => Q (emb b))
      (fun b => R (emb b)) (fun b => A (emb b)) F' ∧
    (∀ b, F' b ⊆ F (emb b) ∧ (0 < lev (emb b) → emb (par' b) = par (emb b))) ∧
    (∀ i γ₁ o, ((lst i γ₁ o).card : ℝ) ≤ N k ^ σ) ∧
    (∀ b, ν k (γ (emb b)) (A (emb b)) ≤
      ENNReal.ofReal (N k ^ σ * N k ^ (-f (r (lev (emb b)))) *
        |Matrix.det (Q (emb b))|) ∧ ∀ p ∈ F' b,
      b ∈ lst (lev (emb b)) (γ (emb b))
        (obs (B k (γ (emb b))) (δ (N k) (r (lev (emb b)))) p)) ∧
    (∀ b, ENNReal.ofReal (ω k (γ (emb b))) *
      ((ν k (γ (emb b))).prod volume) (F' b) ≠ ⊤) ∧
    ∀ a, (∑ b, if 0 < lev (emb b) ∧ par' b = a then
      ENNReal.ofReal (ω k (γ (emb b))) *
        ((ν k (γ (emb b))).prod volume) (F' b) else 0) ≤
      ENNReal.ofReal (ω k (γ (emb a))) *
        ((ν k (γ (emb a))).prod volume) (F' a)

end Submission.Obl.k4_true_forest_own_depth_preparation
