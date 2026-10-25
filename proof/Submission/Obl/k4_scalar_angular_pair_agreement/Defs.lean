import Mathlib
import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces

/-!
# Readable form of `k4_scalar_angular_pair_agreement`

The tuple carrier `Code`, its projections, `Exact`, `ChartData`, `Chart` and
`Cost` are the readable definitions of the accepted obligation o133
(`Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces`); they agree
definitionally with the lambda-bound data of the frozen statement.  Here we add
the pair-certificate predicates of o163 in readable form.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_angular_pair_agreement

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Midpoint of the dyadic interval `I T j`. -/
noncomputable def mid (T : ℕ) (j : Fin (2 ^ T)) : ℝ :=
  ((j : ℕ) + (1 : ℝ) / 2) / (2 : ℝ) ^ T

/-- Whole-box agreement of the predictors of labels `i` and `i'` on the coarse box
over `I T₁ b`, centred at the source label's affine centre. -/
def Agrees (p : Code) (k T₁ n : ℕ) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (a e : ℝ) (b : Fin (2 ^ T₁)) (i i' : Fin n) : Prop :=
  ∀ t ∈ I T₁ b, ∀ z : ℝ, |z - (u i + mid T₁ b * v i)| ≤ ((2 : ℝ) ^ T₁)⁻¹ →
    |MvPolynomial.eval ![t, z] (P i - P i')| ≤ (N p) k ^ (-L p + a * e)

/-- Good two-time pairs of world `w` in the coarse block `b`. -/
def goodPairs (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ) (T₁ : ℕ) (w : Fin (W p k))
    (b : Fin (2 ^ T₁)) : Set ((ℕ × (Fin 5 → ℝ)) × (ℝ × ℝ)) :=
  {z | z.2.1 ∈ I T₁ b ∧ z.2.2 ∈ I T₁ b ∧ ∃ i i' : Fin n, γ i = w ∧ γ i' = w ∧
    I T (j i) ⊆ I T₁ b ∧ I T (j i') ⊆ I T₁ b ∧ (z.1, z.2.1) ∈ C i ∧ (z.1, z.2.2) ∈ C i' ∧
    Agrees p k T₁ n u v P a e b i i'}

/-- The unnormalized original-law good-pair mass. -/
noncomputable def pairMass (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k))
    (j : Fin n → Fin (2 ^ T)) (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ) (T₁ : ℕ) : ENNReal :=
  ∑ w : Fin (W p k), ∑ b : Fin (2 ^ T₁), ENNReal.ofReal (ω p k w) *
    ENNReal.ofReal ((2 : ℝ) ^ T₁) *
    ((ν p k w).prod (MeasureTheory.volume.prod MeasureTheory.volume))
      (goodPairs p k T n γ j C u v P a e T₁ w b)

/-- The pair certificate. -/
def Prepared (p : Code) (h e a : ℝ) : Prop :=
  ∃ B : ℕ, 1 ≤ B ∧ ∀ σ : ℝ, 0 < σ → ∃ᶠ k in Filter.atTop,
    ∃ (T n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
      (A : Fin n → Set (ℕ × (Fin 5 → ℝ))) (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
      (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
      (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)),
      ChartData p B (L p) (L p) (h + σ) σ true k T n γ j A C u v J P Λ ∧
      ∃ T₁ : ℕ, T₁ ≤ T ∧ (2 : ℝ) ^ (T - T₁) ≤ 2 * (N p) k ^ e ∧
        (2 : ℝ) ^ T₁ ≤ 2 * max 1 ((2 : ℝ) ^ T * (N p) k ^ (-e)) ∧
        ENNReal.ofReal ((N p) k ^ (-σ)) ≤ pairMass p k T n γ j C u v P a e T₁

/-- The readable statement of o163. -/
def Statement : Prop :=
  ∀ S₀ η : ℝ, 0 < S₀ → 0 < η → ∃ a c : ℝ, 1 ≤ a ∧ 0 < c ∧
    ∀ p : Code, Exact p → S p = S₀ → U p = η * L p →
      ∀ h e : ℝ, 0 < h → Cost p h → 0 < e → e < h → e < c * L p → Prepared p h e a

end Submission.Obl.k4_scalar_angular_pair_agreement
