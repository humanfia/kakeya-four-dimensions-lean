import Submission.Obl.k4_horizon_chart_assembly.Defs

/-!
Shared from this LOT obligation, session x0559, commit 27dc55d.

Interfaces for the finite-scale / asymptotic cut of the assembly. The finite
statement uses arbitrary probability priors and retains their original masses.
Its complexity is a numerical budget, so no asymptotic quantifiers occur in it.
-/

namespace Submission.Obl.k4_horizon_chart_assembly

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- A chart with an explicit complexity budget and hidden width. -/
def BudgetChart (H : ℝ) (D : ℕ) (κ : ℝ) (T : ℕ) (j a B : ℝ)
    (E : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (R : MvPolynomial (Fin 4) ℝ) (A : Set (ℕ × (Fin 6 → ℝ)))
    (F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (ex : Prop) : Prop :=
  Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ H ∧
  (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ H ∧
  (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧
  R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ H) ∧
  MeasurableSet A ∧ MeasurableSet F ∧
  (∀ i, Fmt 6 H D {x | (i, x) ∈ A} ∧
    Fmt 7 H D {x : Fin 7 → ℝ | ((i, fun e : Fin 6 => x e.castSucc), x 6) ∈ F}) ∧
  (∀ l ∈ A, (l.1 : ℝ) ≤ H ∧ (∀ e, |l.2 e| ≤ H) ∧
    ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T),
      ‖Matrix.toEuclideanLin Q⁻¹ (yl l t - c - t • u)‖ ≤ κ ∧
      |MvPolynomial.eval (xl l t) R| ≤ κ * a ∧
      |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * B ∧
      |MvPolynomial.eval (xl l t)
        (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤
        κ * B ^ 2 / a) ∧
  (∀ p ∈ F, p ∈ E ∧ p.1 ∈ A ∧
    p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧
    B / κ ≤ |MvPolynomial.eval (xl p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) ∧ ex

/-- Original cells are counted with the full original event in each world. -/
def lightMass (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (B : Fin W → ℝ) (a ρ θ : ℝ) : ENNReal :=
  ∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) {p | p ∈ E γ ∧
    ((ν γ).prod volume) {p' | p' ∈ E γ ∧
      ⌊p'.2 / ρ⌋ = ⌊p.2 / ρ⌋ ∧
      ⌊(xl p'.1 p'.2) 1 / ρ⌋ = ⌊(xl p.1 p.2) 1 / ρ⌋ ∧
      ⌊(xl p'.1 p'.2) 2 / ρ⌋ = ⌊(xl p.1 p.2) 2 / ρ⌋ ∧
      (obsl (B γ) a p').2 = (obsl (B γ) a p).2} < ENNReal.ofReal (θ * ρ ^ 3)}

/-- A finite-sample atlas with an explicit residual estimate and a fixed power
of a raw complexity budget. No probability normalization of a group is used. -/
def FiniteWeightedAtlas : Prop :=
  ∃ A C : ℕ, 1 ≤ A ∧ 1 ≤ C ∧
  ∀ ζ : ℝ, 0 < ζ → ∃ η Cg : ℝ, 0 < η ∧ 0 < Cg ∧
  ∀ H K : ℝ, 2 ≤ H → 1 ≤ K → K ≤ H →
  ∀ (W D₀ : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ),
  (W : ℝ) ≤ H → (∀ γ, 0 ≤ ω γ) → (∑ γ, ω γ) = 1 →
  (∀ γ, IsProbabilityMeasure (ν γ) ∧ 0 < B γ ∧ B γ ≤ H ∧ (B γ)⁻¹ ≤ H ∧
    (P γ).totalDegree ≤ 2 ∧ (∀ e, |(P γ).coeff e| ≤ H) ∧
    MeasurableSet (E γ) ∧ E γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
    (∀ p ∈ E γ, (p.1.1 : ℝ) ≤ H ∧ ∀ e, |p.1.2 e| ≤ H) ∧
    (∀ i, Fmt 7 H D₀ {x : Fin 7 → ℝ |
      ((i, fun e : Fin 6 => x e.castSucc), x 6) ∈ E γ})) →
  (∀ γ, ∀ᵐ l ∂ν γ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖yl l t‖ + ‖vl l‖ ≤ K ∧
    |MvPolynomial.eval (xl l t) (P γ)| ≤ K ∧
    |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4) (P γ))| ≤ K * B γ ∧
    |MvPolynomial.eval (xl l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P γ)))| ≤
      K * (B γ) ^ 2) →
  (∀ γ, ∀ᵐ p ∂(((ν γ).prod volume).restrict (E γ)),
    B γ / K ≤ |MvPolynomial.eval (xl p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P γ))|) →
  ∀ (a : ℝ) (T : ℕ), let q : ℝ := ((2 : ℝ) ^ T)⁻¹;
  0 < a → a ≤ 1 → 8 * q ≤ a →
  ∀ Dmesh : ℕ, 2 ≤ Dmesh → H ^ A ≤ (Dmesh : ℝ) →
  ∀ s τ₀ θ n₀ κ : ℝ, 0 < s → 0 < τ₀ → 0 < θ → 0 < n₀ →
  256 * (K + 2) ≤ κ → (Dmesh : ℝ) ^ (-η) ≤ s →
  4 * n₀ * ((2 * K + 2) * q) ^ 2 ≤ τ₀ * κ →
  let V : ℝ := 1 + H + K + (Dmesh : ℝ) + (2 : ℝ) ^ T + τ₀⁻¹;
  ∃ C' : ℕ, ∃ (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T))
    (c u : Fin C' → EuclideanSpace ℝ (Fin 2))
    (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C' → MvPolynomial (Fin 4) ℝ)
    (A' : Fin C' → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)),
    (C' : ℝ) ≤ V ^ C ∧
    (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A' b) (A' b')) ∧
    (∀ b, BudgetChart (V ^ C) (max D₀ 4) κ T ((j b : ℕ) : ℝ) a
      (B (γ b)) (E (γ b)) (c b) (u b) (Q b) (R b) (A' b) (F b)
      (ENNReal.ofReal (n₀ * q * |Matrix.det (Q b)| / κ) ≤
        ((ν (γ b)).prod volume) (F b))) ∧
    (∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (E γ)) ≤
      (∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod volume) (F b)) +
      lightMass W ω ν E B a (q / (Dmesh : ℝ)) θ + ENNReal.ofReal s +
      ENNReal.ofReal (Cg * K ^ 3 * τ₀ * (Dmesh : ℝ) ^ ζ / (s * θ * q ^ 2)) *
        (∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (E γ))

end
end Submission.Obl.k4_horizon_chart_assembly
