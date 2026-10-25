import Submission.Obl.k4_scalar_uniform_terminal_extension.Defs

/-!
The intermediate certificate records a positive amount of original two-time mass.
It contains old charts and comparisons, before any new assignment or atlas exists.
-/

namespace Submission.Obl.k4_scalar_uniform_terminal_extension

open MeasureTheory

/-- Midpoint of a dyadic block. -/
noncomputable def mid (T : ℕ) (j : Fin (2 ^ T)) : ℝ :=
  ((j : ℕ) + (1 : ℝ) / 2) / (2 : ℝ) ^ T

/-- Agreement on a whole static box centered at the source chart's midpoint. -/
def Agrees (p : Problem) (k T₁ n : ℕ) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ)
    (b : Fin (2 ^ T₁)) (i i' : Fin n) : Prop :=
  ∀ t ∈ I T₁ b, ∀ z : ℝ,
    |z - (u i + mid T₁ b * v i)| ≤ ((2 : ℝ) ^ T₁)⁻¹ →
    |MvPolynomial.eval ![t, z] (P i - P i')| ≤ (N p) k ^ (-L p + a * e)

/-- Source and witness are selected old incidences of the same original trajectory. -/
def goodPairs (p : Problem) (k T n : ℕ)
    (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
    (C : Fin n → Set Incidence) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ)
    (T₁ : ℕ) (w : Fin (W p k)) (b : Fin (2 ^ T₁)) : Set (Trajectory × (ℝ × ℝ)) :=
  {z | z.2.1 ∈ I T₁ b ∧ z.2.2 ∈ I T₁ b ∧
    ∃ i i' : Fin n, γ i = w ∧ γ i' = w ∧
      I T (j i) ⊆ I T₁ b ∧ I T (j i') ⊆ I T₁ b ∧
      (z.1, z.2.1) ∈ C i ∧ (z.1, z.2.2) ∈ C i' ∧
      Agrees p k T₁ n u v P a e b i i'}

/-- The block weight q₁ and the two normalized time priors give the factor 1/q₁. -/
noncomputable def pairMass (p : Problem) (k T n : ℕ)
    (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
    (C : Fin n → Set Incidence) (u v : Fin n → ℝ)
    (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ) (T₁ : ℕ) : ENNReal :=
  ∑ w : Fin (W p k), ∑ b : Fin (2 ^ T₁),
    ENNReal.ofReal (ω p k w) * ENNReal.ofReal ((2 : ℝ) ^ T₁) *
      ((ν p k w).prod (volume.prod volume))
        (goodPairs p k T n γ j C u v P a e T₁ w b)

/-- One exponent controls old-chart complexity at arbitrarily small loss.
The fitting allowance `a * e` is fixed before that loss tends to zero. -/
def Prepared (p : Problem) (h e a : ℝ) : Prop :=
  ∃ B : ℕ, 1 ≤ B ∧ ∀ σ : ℝ, 0 < σ → ∃ᶠ k in Filter.atTop,
    ∃ (T n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
      (A : Fin n → Set Trajectory) (C : Fin n → Set Incidence)
      (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
      (Λ : Fin (W p k) → Observation → Finset (Fin n)),
      ChartData p B (L p) (L p) (h + σ) σ true k T n γ j A C u v J P Λ ∧
      ∃ T₁ : ℕ, T₁ ≤ T ∧
        (2 : ℝ) ^ (T - T₁) ≤ 2 * (N p) k ^ e ∧
        (2 : ℝ) ^ T₁ ≤ 2 * max 1 ((2 : ℝ) ^ T * (N p) k ^ (-e)) ∧
        ENNReal.ofReal ((N p) k ^ (-σ)) ≤ pairMass p k T n γ j C u v P a e T₁

/-- Quantitative original-law comparison, using the joint terminal/angular ceiling. -/
def AngularPairs : Prop :=
  ∀ S₀ η : ℝ, 0 < S₀ → 0 < η →
    ∃ a c : ℝ, 1 ≤ a ∧ 0 < c ∧ ∀ p : Problem,
      Exact p → S p = S₀ → U p = η * L p →
      ∀ h e : ℝ, 0 < h → Cost p h → 0 < e → e < h → e < c * L p →
      Prepared p h e a

/-- Source-time selection and finite quadratic coefficient bins assemble the atlas. -/
def PairAssembly : Prop :=
  ∀ p : Problem, Exact p → ∀ h e a : ℝ,
    0 < e → e < h → 1 ≤ a → 0 < L p - (a + 10) * e →
    Prepared p h e a → Known p (L p - (a + 10) * e) (L p) (h - e)

end Submission.Obl.k4_scalar_uniform_terminal_extension
