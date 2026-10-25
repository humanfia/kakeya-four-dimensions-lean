-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/Certificates.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Certificates.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.Interface

set_option linter.unusedVariables false

namespace Submission.Obl.k4_clean_cover_graph_atlas

/-- A finite geometric family with whole-block closeness to quadratic roots.
The derivative scale is stable but is not yet normalized to the final chart allowance. -/
def GraphAtlas
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (r₀ h θ β : ℝ) (M D T C : ℕ)
    (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T))
    (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (P : Fin C → MvPolynomial (Fin 4) ℝ) (scale : Fin C → ℝ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)) : Prop :=
  (C : ℝ) ≤ Nk ^ M ∧
  (∀ w, 0 < B w ∧ B w ≤ Nk ^ M ∧ (B w)⁻¹ ≤ Nk ^ M) ∧
  (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
  (∀ w o, ((lst w o).card : ℝ) ≤ Nk ^ β) ∧
  (∀ w b, MeasurableSet {o | b ∈ lst w o}) ∧
  (∀ b, Matrix.det (Q b) ≠ 0 ∧
    ‖c b‖ + ‖u b‖ ≤ Nk ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, (|Q b e e'| + |(Q b)⁻¹ e e'|)) ≤ Nk ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, |Q b e e'|) ≤ Nk ^ β / (2 : ℝ) ^ T ∧
    (P b).totalDegree ≤ 2 ∧ (∀ e, |(P b).coeff e| ≤ Nk ^ M) ∧
    0 < scale b ∧ scale b ≤ Nk ^ M ∧ (scale b)⁻¹ ≤ Nk ^ M ∧
    MeasurableSet (A b) ∧ MeasurableSet (F b) ∧
    (∀ i, fmt 6 (Nk ^ M) D {z | (i, z) ∈ A b} ∧
      fmt 7 (Nk ^ M) D {z : Fin 7 → ℝ |
        ((i, fun a : Fin 6 => z a.castSucc), z 6) ∈ F b}) ∧
    (∀ l ∈ A b, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧
      ∀ t ∈ Set.Icc ((j b : ℕ) / (2 : ℝ) ^ T) (((j b : ℕ) + 1) / (2 : ℝ) ^ T),
        ‖Matrix.toEuclideanLin (Q b)⁻¹ (y l t - c b - t • u b)‖ ≤ Nk ^ β) ∧
    (∀ p ∈ F b, p ∈ E (γ b) ∧ p.1 ∈ A b ∧
      p.2 ∈ Set.Icc ((j b : ℕ) / (2 : ℝ) ^ T) (((j b : ℕ) + 1) / (2 : ℝ) ^ T)) ∧
    (∀ l ∈ A b,
      ∀ t ∈ Set.Icc ((j b : ℕ) / (2 : ℝ) ^ T) (((j b : ℕ) + 1) / (2 : ℝ) ^ T),
      ∃ w₀ : ℝ,
        |(x l t) 3 - w₀| ≤ δ Nk r₀ / B (γ b) * Nk ^ (-(θ * h * L)) ∧
        MvPolynomial.eval (Function.update (x l t) (3 : Fin 4) w₀) (P b) = 0 ∧
        scale b / 2 ≤ |MvPolynomial.eval (Function.update (x l t) (3 : Fin 4) w₀)
          (MvPolynomial.pderiv (3 : Fin 4) (P b))| ∧
        |MvPolynomial.eval (Function.update (x l t) (3 : Fin 4) w₀)
          (MvPolynomial.pderiv (3 : Fin 4) (P b))| ≤ 2 * scale b)) ∧
  ENNReal.ofReal (Nk ^ (-β)) ≤ ∑ b, ENNReal.ofReal (ω (γ b)) *
    ((ν (γ b)).prod MeasureTheory.volume)
      {p | p ∈ F b ∧ b ∈ lst (γ b) (obs (B (γ b)) (δ Nk L) p)}

/-- The output atlas clauses that do not concern its relation to an old depth. -/
def RealizedAtlas
    (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (r₂ ζ : ℝ) (M D T C : ℕ)
    (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T))
    (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)) : Prop :=
  (C : ℝ) ≤ Nk ^ M ∧
  (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
  (∀ w o, ((lst w o).card : ℝ) ≤ Nk ^ ζ) ∧
  (∀ w b, MeasurableSet {o | b ∈ lst w o}) ∧
  (∀ b, chart Nk M D (Nk ^ ζ) T ((j b : ℕ) : ℝ) r₂ (B (γ b)) (E (γ b))
    (c b) (u b) (Q b) (R b) (A b) (F b) True) ∧
  ENNReal.ofReal (Nk ^ (-ζ)) ≤ ∑ b, ENNReal.ofReal (ω (γ b)) *
    ((ν (γ b)).prod MeasureTheory.volume)
      {p | p ∈ F b ∧ b ∈ lst (γ b) (obs (B (γ b)) (δ Nk L) p)}

/-- Analytical preparation stops before normalizing representative equations. -/
def Preparation : Prop :=
  localGraph → stableSheets → algebraicRemez →
  ∀ d₁ κ₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
  ∃ θ ρ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ 0 < ρ ∧ d₁ + ρ < 1 ∧
  ∀ S η : ℝ, 0 < S → 0 < η →
  ∀ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ),
    (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) →
    0 < gain → gain ≤ 1 / 8 → 0 < δ₀ → δ₀ ≤ ρ * gain →
  ∀ N K L d W ω ν E P B f g G,
    prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
  ∀ Mp Dp Mg Dg : ℕ, ∃ M D : ℕ,
  ∀ β : ℝ, 0 < β → β ≤ 1 →
  ∃ ε σ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ β ∧ 0 < σ ∧
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
  ∀ r T nw κ C lev par γ j c u Q R A F lst,
    path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ
      r T nw κ C lev par γ j c u Q R A F lst →
    greedyCover (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T C lev γ j A F Mg Dg ε →
  ∃ (i : ℕ) (h : ℝ) (T₂ C₂ : ℕ)
    (γ₂ : Fin C₂ → Fin (W k)) (j₂ : Fin C₂ → Fin (2 ^ T₂))
    (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2))
    (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ)
    (P₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ) (scale : Fin C₂ → ℝ)
    (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ)))
    (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst₂ : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
    i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧ r i + 2 * h * L ≤ L ∧
    (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * (N k) ^ (κ₁ * ((θ / 4) * gain) * L / 2) ∧
    GraphAtlas (N k) L (W k) (ω k) (ν k) (E k) (B k)
      (r i) h θ β M D T₂ C₂ γ₂ j₂ c₂ u₂ Q₂ P₂ scale A₂ F₂ lst₂

/-- Uniform realization of any graph atlas, independent of analytical input. -/
def Realization : Prop :=
  ∀ M : ℕ, ∃ M' : ℕ, M ≤ M' ∧
  ∀ L θ gain ζ : ℝ, 0 < L → 0 < θ → θ ≤ 1 / 4 →
    0 < gain → gain ≤ 1 / 8 → 0 < ζ → ζ ≤ 1 →
  ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ Nk : ℝ, N₀ ≤ Nk →
  ∀ (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (r₀ h β : ℝ) (D T C : ℕ)
    (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T))
    (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (P : Fin C → MvPolynomial (Fin 4) ℝ) (scale : Fin C → ℝ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)),
    0 ≤ r₀ → gain ≤ h → h ≤ 1 / 8 → r₀ + 2 * h * L ≤ L →
    0 < β → β ≤ ζ / 4 →
    GraphAtlas Nk L W ω ν E B r₀ h θ β M D T C γ j c u Q P scale A F lst →
  ∃ (r₂ : ℝ) (C₂ : ℕ)
    (γ₂ : Fin C₂ → Fin W) (j₂ : Fin C₂ → Fin (2 ^ T))
    (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2))
    (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ)
    (R₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ)
    (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ)))
    (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst₂ : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
    r₀ + (θ / 4) * gain * L ≤ r₂ ∧ r₂ + (θ / 4) * gain * L ≤ L ∧
    RealizedAtlas Nk L W ω ν E B r₂ ζ M' D T C₂ γ₂ j₂ c₂ u₂ Q₂ R₂ A₂ F₂ lst₂

end Submission.Obl.k4_clean_cover_graph_atlas
