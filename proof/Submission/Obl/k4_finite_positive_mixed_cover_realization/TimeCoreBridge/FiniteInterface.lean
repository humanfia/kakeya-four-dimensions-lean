-- Adapted from this LOT tree, o210, session x0795, commit f6d85510,
-- Submission/Obl/k4_clean_cover_graph_atlas/FiniteInterface.lean. Earlier provenance is retained below.
-- The path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0684, SplitInterfaces.lean,
-- commit d640557e. Definitions restricted to the finite construction.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Certificates

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

/-- The fixed old depth and fixed candidate depth used for density deletion. -/
def menuDepth (L s h δ₀ : ℝ) : ℝ :=
  min L (max 0 (s * L + h * L - 2 * δ₀ * L))

/-- Finite data needed in addition to a path. Its exponent is fixed before the output allowance. -/
def ScalarData (Nk : ℝ) (M D W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) : Prop :=
  (W : ℝ) ≤ Nk ^ M ∧ (∀ w, 0 ≤ ω w) ∧ (∑ w, ω w) = 1 ∧
  ∀ w, MeasureTheory.IsProbabilityMeasure (ν w) ∧
    0 < B w ∧ B w ≤ Nk ^ M ∧ (B w)⁻¹ ≤ Nk ^ M ∧ MeasurableSet (E w) ∧
    ∀ q, fmt 7 (Nk ^ M) D
      {z : Fin 7 → ℝ | ((q, fun a : Fin 6 => z a.castSucc), z 6) ∈ E w}

/-- A greedy witness cleaned under the original laws. Each retained candidate keeps half
its original full-packet floor; its old packet also keeps half its saturation floor.
The three observation ceilings are at fixed menu depths and at the original terminal depth. -/
def CleanCover (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (B : Fin W → ℝ)
    (f : ℝ → ℝ) (d₁ ρ gain δ₀ : ℝ) (m : ℕ) (s r : ℕ → ℝ) (T : ℕ → ℕ)
    (κ : ℝ) (C : ℕ) (lev : Fin C → ℕ) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Mg Dg : ℕ) (τ ε : ℝ) : Prop :=
  ∃ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C)
    (R' : Fin n → MvPolynomial (Fin 4) ℝ)
    (A' : Fin n → Set (ℕ × (Fin 6 → ℝ)))
    (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (U : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
    i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧ (∃ z : ℕ, h = gain + (z : ℝ) * (ρ * gain)) ∧
    r i + 2 * h * L ≤ L ∧ (n : ℝ) ≤ Nk ^ Mg ∧
    (∀ a, lev (old a) = i ∧ 0 < ν (γ (old a)) (A (old a)) ∧
      (R' a).totalDegree ≤ 2 ∧ (∀ e, |(R' a).coeff e| ≤ Nk ^ Mg) ∧
      MeasurableSet (A' a) ∧ A' a ⊆ A (old a) ∧
      (∀ q, fmt 6 (Nk ^ Mg) Dg {z | (q, z) ∈ A' a}) ∧
      (∀ l ∈ A' a,
        ∀ t ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i)
          (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i),
          |MvPolynomial.eval (x l t) (R' a)| ≤
            Nk ^ (4 * ρ * gain * L + 4 * ε) * δ Nk (r i + h * L) ∧
          |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (R' a))| ≤
            Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ∧
          |MvPolynomial.eval (x l t)
            (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (R' a)))| ≤
            Nk ^ (4 * ρ * gain * L + 4 * ε) * B (γ (old a)) ^ 2 / δ Nk (r i + h * L)) ∧
      MeasurableSet (V a) ∧
      V a ⊆ {p | p ∈ U (old a) ∧ p.1 ∈ A' a ∧
        p.2 ∈ Set.Icc ((j (old a) : ℝ) / (2 : ℝ) ^ T i)
          (((j (old a) : ℝ) + 1) / (2 : ℝ) ^ T i) ∧
        B (γ (old a)) / Nk ^ (4 * ρ * gain * L + 4 * ε) ≤
          |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (R' a))|} ∧
      ENNReal.ofReal (Nk ^ (-((d₁ * h + 4 * ρ * gain) * L) - 4 * ε) /
        (2 * (2 : ℝ) ^ T i)) * ν (γ (old a)) (A (old a)) ≤
          ((ν (γ (old a))).prod MeasureTheory.volume) (V a) ∧
      ENNReal.ofReal (Nk ^ (-f (r i)) * |Matrix.det (Q (old a))| /
        (2 * (2 : ℝ) ^ T i * κ)) ≤
          ((ν (γ (old a))).prod MeasureTheory.volume) (U (old a)) ∧
      (((ν (γ (old a))).prod MeasureTheory.volume).restrict (V a)).map
          (obs (B (γ (old a))) (δ Nk (menuDepth L (s i) h δ₀))) ≤
        ENNReal.ofReal (Nk ^ (-f (menuDepth L (s i) h δ₀) + τ)) •
          (MeasureTheory.volume.prod MeasureTheory.Measure.count) ∧
      (((ν (γ (old a))).prod MeasureTheory.volume).restrict (V a)).map
          (obs (B (γ (old a))) (δ Nk L)) ≤
        ENNReal.ofReal (Nk ^ (-f L + τ)) •
          (MeasureTheory.volume.prod MeasureTheory.Measure.count)) ∧
    (∀ b, MeasurableSet (U b) ∧ U b ⊆ F b ∧
      (((ν (γ b)).prod MeasureTheory.volume).restrict (U b)).map
          (obs (B (γ b)) (δ Nk (menuDepth L (s i) 0 δ₀))) ≤
        ENNReal.ofReal (Nk ^ (-f (menuDepth L (s i) 0 δ₀) + τ)) •
          (MeasureTheory.volume.prod MeasureTheory.Measure.count)) ∧
    (∀ a a', a ≠ a' → old a = old a' → Disjoint (A' a) (A' a')) ∧
    (∀ b : Fin C, ((Finset.univ.filter (fun a => old a = b)).card : ℝ) ≤
      Nk ^ ((d₁ * h + 4 * ρ * gain) * L + 4 * ε)) ∧
    (∀ a a', a ≠ a' → γ (old a) = γ (old a') → Disjoint (V a) (V a')) ∧
    ENNReal.ofReal (Nk ^ (-ε) / 2) ≤
      ∑ a, ENNReal.ofReal (ω (γ (old a))) *
        ((ν (γ (old a))).prod MeasureTheory.volume) (V a)

/-- The finite analytic construction after original-law density cleaning. It has no
sequence, asymptotic density, angular law, or final representative normalization. -/
def FiniteConstruction : Prop :=
  localGraph → stableSheets → algebraicRemez →
  ∀ d₁ κ₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
  ∃ θ ρ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ 0 < ρ ∧ ρ ≤ 1 / 4 ∧ d₁ + ρ < 1 ∧
  ∀ (L : ℝ) (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), 0 < L →
    (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) →
    0 < gain → gain ≤ 1 / 8 → 0 < δ₀ → δ₀ ≤ ρ * gain →
  ∀ Mp Dp Mg Dg Mpr Dpr : ℕ, ∃ M D : ℕ,
  ∀ β : ℝ, 0 < β → β ≤ 1 →
  ∃ τ ε₀ σ₀ : ℝ, 0 < τ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < σ₀ ∧ σ₀ ≤ 1 ∧
  ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ Nk : ℝ, N₀ ≤ Nk →
  ∀ (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ)
    (f : ℝ → ℝ), ScalarData Nk Mpr Dpr W ω ν E B →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
  ∀ ε σ : ℝ, 0 < ε → ε ≤ ε₀ → ε ≤ β → 0 < σ → σ ≤ σ₀ →
  ∀ r T nw κ C lev par γ j c u Q R A F lst,
    path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ
      r T nw κ C lev par γ j c u Q R A F lst →
    CleanCover Nk L W ω ν B f d₁ ρ gain δ₀ m s r T κ C lev γ j Q A F Mg Dg τ ε →
  ∃ (i : ℕ) (h : ℝ) (T₂ C₂ : ℕ)
    (γ₂ : Fin C₂ → Fin W) (j₂ : Fin C₂ → Fin (2 ^ T₂))
    (c₂ u₂ : Fin C₂ → EuclideanSpace ℝ (Fin 2))
    (Q₂ : Fin C₂ → Matrix (Fin 2) (Fin 2) ℝ)
    (P₂ : Fin C₂ → MvPolynomial (Fin 4) ℝ) (scale : Fin C₂ → ℝ)
    (A₂ : Fin C₂ → Set (ℕ × (Fin 6 → ℝ)))
    (F₂ : Fin C₂ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst₂ : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C₂)),
    i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧ r i + 2 * h * L ≤ L ∧
    (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * ((θ / 4) * gain) * L / 2) ∧
    GraphAtlas Nk L W ω ν E B (r i) h θ β M D T₂ C₂ γ₂ j₂ c₂ u₂ Q₂ P₂ scale A₂ F₂ lst₂

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
