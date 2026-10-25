-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/Core.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0581, commit 793edcb4e591,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Core.lean.

import Submission.Obl.k4_clean_cover_graph_atlas.Entries
import Submission.Obl.k4_clean_cover_graph_atlas.FiniteInterface

/-!
# The analytic core and the preparation certificate

`CoreOutput` is everything the analysis must supply at one sample, beyond the path and the greedy
cover: a finite bin type `Λ`, a bin for every entry, a representative quadratic and scale for every
label (entry group × bin), lists at the terminal observation, and covered incidences for every entry
lying in the entry's lines on its sub-block, whose lines pass the root tests of their label, with
list success `≥ N^{-β}`.

`Core` is the analytic statement, in the quantifier order of `Preparation`, whose sample conclusion
re-exports the greedy data and gives the sub-block exponent `s₀`, the box range `K` and a
`CoreOutput`. `preparation_of_core` proves `Preparation` from `Core` (`Entries.graphAtlas_of_entries`
does the chart assembly; the rest is quantifier bookkeeping and polynomial counting).
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- The analytic output at one sample. -/
def CoreOutput (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))) (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (B : Fin W → ℝ) (r₀ h θ β : ℝ) (Mc : ℕ)
    {C : ℕ} (γ : Fin C → Fin W) (j : Fin C → ℕ) (c u : Fin C → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C → MvPolynomial (Fin 4) ℝ)
    {n : ℕ} (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
    (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (Ti s₀ K : ℕ) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (binOf : Entry n s₀ K → Λ)
    (P : (Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) × Λ → MvPolynomial (Fin 4) ℝ)
    (s m₀ : (Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) × Λ → ℝ)
    (lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) →
      Finset ((Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool) × Λ))
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
    (Fintype.card Λ : ℝ) ≤ Nk ^ Mc ∧
    (∀ ℓ, (P ℓ).totalDegree ≤ 2) ∧ (∀ ℓ e, |(P ℓ).coeff e| ≤ Nk ^ Mc) ∧
    (∀ ℓ, 0 < s ℓ ∧ s ℓ ≤ Nk ^ Mc ∧ (s ℓ)⁻¹ ≤ Nk ^ Mc) ∧
    (∀ ℓ, 0 ≤ m₀ ℓ ∧ m₀ ℓ ≤ rootThreshold Nk r₀ h θ L (B (γ ℓ.1.1)) (s ℓ)) ∧
    (∀ ℓ, |qc (P ℓ)| * m₀ ℓ ≤ s ℓ ^ 2 / 40) ∧
    (∀ e, cov e ⊆ {p | p ∈ E (γ (old e.1)) ∧
      p.1 ∈ memE old R' A' j c u Q R Ti s₀ K e ∧ p.2 ∈ subBlock Ti s₀ (j (old e.1)) e.2.1}) ∧
    (∀ e, ∀ p ∈ cov e, p.1 ∈ rootTestSet (P (entryGroup old e, binOf e))
      (s (entryGroup old e, binOf e)) (m₀ (entryGroup old e, binOf e))
      ((subIdx s₀ (j (old e.1)) e.2.1 : ℝ) / (2 : ℝ) ^ (Ti + s₀))
      (((subIdx s₀ (j (old e.1)) e.2.1 : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀))) ∧
    (∀ w o, ((lst w o).card : ℝ) ≤ Nk ^ β) ∧
    (∀ w ℓ, MeasurableSet {o | ℓ ∈ lst w o}) ∧
    ENNReal.ofReal (Nk ^ (-β)) ≤ ∑ ℓ, ENNReal.ofReal (ω (γ ℓ.1.1)) *
      ((ν (γ ℓ.1.1)).prod volume) {p | (∃ e, (entryGroup old e, binOf e) = ℓ ∧ p ∈ cov e) ∧
        ℓ ∈ lst (γ ℓ.1.1) (obs (B (γ ℓ.1.1)) (δ Nk L) p)}

/-- The finite analytic construction, with the geometric output kept as a label system.
The exponent `Mc` controls the auxiliary subdivision, box range, bins, representatives,
and derivative scales before the output allowance is chosen. -/
def FiniteCore : Prop :=
  localGraph → stableSheets → algebraicRemez →
  ∀ d₁ κ₁ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
  ∃ θ ρ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ 0 < ρ ∧ ρ ≤ 1 / 4 ∧ d₁ + ρ < 1 ∧
  ∀ (L : ℝ) (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), 0 < L →
    (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) →
    0 < gain → gain ≤ 1 / 8 → 0 < δ₀ → δ₀ ≤ ρ * gain →
  ∀ Mp Dp Mg Dg Mpr Dpr : ℕ, ∃ Mc : ℕ,
  ∀ β : ℝ, 0 < β → β ≤ 1 →
  ∃ τ ε₀ σ₀ : ℝ, 0 < τ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < σ₀ ∧ σ₀ ≤ 1 ∧ σ₀ ≤ β / 2 ∧
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
  ∃ (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
    (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (s₀ K' : ℕ),
    i < m ∧ gain ≤ h ∧ h ≤ 1 / 8 ∧ r i + 2 * h * L ≤ L ∧
    (n : ℝ) ≤ Nk ^ Mg ∧
    (∀ a, lev (old a) = i ∧ (R' a).totalDegree ≤ 2 ∧ A' a ⊆ A (old a) ∧
      ∀ q, fmt 6 (Nk ^ Mg) Dg {z | (q, z) ∈ A' a}) ∧
    (∀ a a', a ≠ a' → old a = old a' → Disjoint (A' a) (A' a')) ∧
    (2 : ℝ) ^ (T i + s₀) ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * ((θ / 4) * gain) * L / 2) ∧
    (2 : ℝ) ^ s₀ ≤ Nk ^ Mc ∧ (K' : ℝ) ≤ Nk ^ Mc ∧
    CoreOutput Nk L W ω ν E B (r i) h θ β Mc γ j c u Q R old R' A' (T i) s₀ K'

end Submission.Obl.k4_clean_cover_graph_atlas
