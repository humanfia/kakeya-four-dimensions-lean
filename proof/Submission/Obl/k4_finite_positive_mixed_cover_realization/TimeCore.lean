-- `GraphAtlas` and `ScalarData` are adapted from this LOT tree, o210, session x0795,
-- commit fbf73848, Submission/Obl/k4_clean_cover_graph_atlas/Certificates.lean and
-- FiniteInterface.lean (there adapted from o194, session x0672, commit 69d09a7b8755, and
-- o173, session x0598, commit 6ded8016fe11). `TimeCore` is o210's frozen
-- `FiniteConstruction` with its zero-narrowness path replaced by `PositivePath ℓ`.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.Interface
import Submission.Obl.k4_fixed_menu_density_pruning.Interface

/-!
# The analytic core of the time branch

`TimeCore` is the only analytic input of the time branch: o210's frozen statement
(`k4_clean_cover_graph_atlas`, the graph-atlas construction from a density-cleaned greedy
quadratic cover) for the positive-narrowness path of o234. The narrowness `nw` occurs in the
path only through the conjunct `|nw i - ℓ * s i * L| ≤ δ₀ * L` and the determinant bounds of
the path charts; o210's construction never uses that conjunct, so its proof transfers.

The analytic premises of o210 (local graph matching, stable hidden sheets, algebraic Remez)
are accepted theorems (o112, o171, o172); `TimeCore` keeps only `Matching`, from which o112
derives local graph matching.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

noncomputable section

/-- The cleaned cover of o209's split (the accepted density pruning, o209). -/
abbrev CleanCover := Submission.Obl.k4_fixed_menu_density_pruning.CleanCover

/-- Finite data needed in addition to a path. -/
def ScalarData (Nk : ℝ) (M D W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) : Prop :=
  (W : ℝ) ≤ Nk ^ M ∧ (∀ w, 0 ≤ ω w) ∧ (∑ w, ω w) = 1 ∧
  ∀ w, MeasureTheory.IsProbabilityMeasure (ν w) ∧
    0 < B w ∧ B w ≤ Nk ^ M ∧ (B w)⁻¹ ≤ Nk ^ M ∧ MeasurableSet (E w) ∧
    ∀ q, fmt 7 (Nk ^ M) D
      {z : Fin 7 → ℝ | ((q, fun a : Fin 6 => z a.castSucc), z 6) ∈ E w}

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

/-- **The analytic core of the time branch**: o210's frozen `FiniteConstruction` for the
positive-narrowness path. -/
def TimeCore : Prop :=
  Matching →
  ∀ ℓ d₁ κ₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
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
    PositivePath ℓ Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ
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

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
