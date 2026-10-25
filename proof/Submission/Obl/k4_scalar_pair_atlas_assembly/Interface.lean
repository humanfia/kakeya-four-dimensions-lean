import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_pair_atlas_assembly

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-- Midpoint of a coarse dyadic time interval. -/
def mid (T : ℕ) (j : Fin (2 ^ T)) : ℝ :=
  ((j : ℕ) + (1 : ℝ) / 2) / (2 : ℝ) ^ T

/-- Whole-box agreement, with the box centered on the old source chart. -/
def Agrees (p : Code) (k T₁ n : ℕ) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ)
    (b : Fin (2 ^ T₁)) (i i' : Fin n) : Prop :=
  ∀ t ∈ I T₁ b, ∀ z : ℝ,
    |z - (u i + mid T₁ b * v i)| ≤ ((2 : ℝ) ^ T₁)⁻¹ →
    |MvPolynomial.eval ![t, z] (P i - P i')| ≤ N p k ^ (-L p + a * e)

/-- The pair event uses two original incidences on a single trajectory. -/
def goodPairs (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k))
    (j : Fin n → Fin (2 ^ T))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (a e : ℝ) (T₁ : ℕ) (w : Fin (W p k)) (b : Fin (2 ^ T₁)) :
    Set ((ℕ × (Fin 5 → ℝ)) × (ℝ × ℝ)) :=
  {z | z.2.1 ∈ I T₁ b ∧ z.2.2 ∈ I T₁ b ∧
    ∃ i i' : Fin n, γ i = w ∧ γ i' = w ∧
      I T (j i) ⊆ I T₁ b ∧ I T (j i') ⊆ I T₁ b ∧
      (z.1, z.2.1) ∈ C i ∧ (z.1, z.2.2) ∈ C i' ∧
      Agrees p k T₁ n u v P a e b i i'}

/-- Inverse-time-width normalization of the original-law pair event. -/
def pairMass (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k))
    (j : Fin n → Fin (2 ^ T))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (a e : ℝ) (T₁ : ℕ) : ENNReal :=
  ∑ w : Fin (W p k), ∑ b : Fin (2 ^ T₁),
    ENNReal.ofReal (ω p k w) * ENNReal.ofReal ((2 : ℝ) ^ T₁) *
      ((ν p k w).prod (volume.prod volume))
        (goodPairs p k T n γ j C u v P a e T₁ w b)

/-- A fixed old complexity exponent works for every positive loss. -/
def Prepared (p : Code) (h e a : ℝ) : Prop :=
  ∃ B : ℕ, 1 ≤ B ∧ ∀ σ : ℝ, 0 < σ → ∃ᶠ k in atTop,
    ∃ (T n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
      (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
      (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
      (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
      (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)),
      ChartData p B (L p) (L p) (h + σ) σ true k T n γ j A C u v J P Λ ∧
      ∃ T₁ : ℕ, T₁ ≤ T ∧ (2 : ℝ) ^ (T - T₁) ≤ 2 * N p k ^ e ∧
        (2 : ℝ) ^ T₁ ≤ 2 * max 1 ((2 : ℝ) ^ T * N p k ^ (-e)) ∧
        ENNReal.ofReal (N p k ^ (-σ)) ≤ pairMass p k T n γ j C u v P a e T₁

end

end Submission.Obl.k4_scalar_pair_atlas_assembly
