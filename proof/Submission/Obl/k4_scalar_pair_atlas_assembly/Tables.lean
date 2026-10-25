import Submission.Obl.k4_scalar_pair_atlas_assembly.Interface

-- Adapted from this LOT obligation, x0578/093ea34, Interface.lean.
-- We retain the existing accepted o133 scalar base interface used by the helper modules.
set_option autoImplicit false

namespace Submission.Obl.k4_scalar_pair_atlas_assembly

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-- A table is fixed before the source fine blocks are selected. Every old source
has one output code; the full source assignment fits that representative. -/
def Table (p : Code) (k G : ℕ) (r ε : ℝ) (T T₁ n : ℕ)
    (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
    (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
    (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ) (a e : ℝ)
    (m : ℕ) (g : Fin m → Fin (W p k)) (b : Fin m → Fin (2 ^ T₁))
    (code : Fin n → Fin m) (u' v' J' : Fin m → ℝ)
    (P' : Fin m → MvPolynomial (Fin 2) ℝ)
    (R : Fin n → Finset (Fin m)) : Prop :=
  (m : ℝ) ≤ N p k ^ (G : ℝ) ∧
  (∀ i, g (code i) = γ i ∧ I T (j i) ⊆ I T₁ (b (code i))) ∧
  (∀ o, 0 < J' o ∧ (J' o)⁻¹ ≤ N p k ^ (G : ℝ) ∧
    J' o ≤ N p k ^ ε / (2 : ℝ) ^ T₁ ∧ |u' o| + |v' o| ≤ N p k ^ ε ∧
    (P' o).totalDegree ≤ 2 ∧ ∀ c, |(P' o).coeff c| ≤ N p k ^ (G : ℝ)) ∧
  (∀ i, ∀ l ∈ A i, ∀ t ∈ I T₁ (b (code i)),
    |y l t - u' (code i) - t * v' (code i)| ≤ N p k ^ ε * J' (code i) ∧
    |x l t - MvPolynomial.eval ![t, y l t] (P' (code i))| ≤
      N p k ^ ε * N p k ^ (-r)) ∧
  (∀ i, ((R i).card : ℝ) ≤ N p k ^ (ε / 2)) ∧
  (∀ i o, o ∈ R i → g o = γ i ∧ I T (j i) ⊆ I T₁ (b o)) ∧
  (∀ i i', γ i = γ i' → ∀ c : Fin (2 ^ T₁),
    I T (j i) ⊆ I T₁ c → I T (j i') ⊆ I T₁ c →
    (A i ∩ A i').Nonempty → Agrees p k T₁ n u v P a e c i i' →
    code i ∈ R i')

/-- Geometry and coding only: no new source assignment or incidence set is selected. -/
def SparseTables : Prop :=
  ∀ p : Code, Exact p → ∀ h e a : ℝ,
    0 < e → e < h → 1 ≤ a → 0 < L p - (a + 10) * e →
    ∀ B : ℕ, 1 ≤ B → ∃ G : ℕ, 1 ≤ G ∧
    ∀ ε : ℝ, 0 < ε → ∃ σ : ℝ, 0 < σ ∧ σ ≤ ε / 2 ∧
    ∀ᶠ k in atTop,
    ∀ (T n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
      (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
      (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
      (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
      (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)),
    ChartData p B (L p) (L p) (h + σ) σ true k T n γ j A C u v J P Λ →
    ∀ T₁ : ℕ, T₁ ≤ T → (2 : ℝ) ^ (T - T₁) ≤ 2 * N p k ^ e →
      (2 : ℝ) ^ T₁ ≤ 2 * max 1 ((2 : ℝ) ^ T * N p k ^ (-e)) →
    ∃ (m : ℕ) (g : Fin m → Fin (W p k)) (b : Fin m → Fin (2 ^ T₁))
      (code : Fin n → Fin m) (u' v' J' : Fin m → ℝ)
      (P' : Fin m → MvPolynomial (Fin 2) ℝ) (R : Fin n → Finset (Fin m)),
      Table p k G (L p - (a + 10) * e) ε T T₁ n γ j A u v P a e
        m g b code u' v' J' P' R

/-- Source-block averaging, finite format, pruning and terminal-list installation. -/
def InstallTables : Prop :=
  ∀ p : Code, Exact p → ∀ B G : ℕ, 1 ≤ B → 1 ≤ G →
    ∃ B' : ℕ, 1 ≤ B' ∧ ∀ h₀ h₁ r ε σ a e : ℝ,
    0 < ε → 0 < σ → σ ≤ ε / 2 →
    ∀ (k T T₁ n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
      (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
      (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
      (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
      (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)),
    ChartData p B (L p) (L p) h₀ σ true k T n γ j A C u v J P Λ →
    T₁ ≤ T → (2 : ℝ) ^ T₁ ≤ N p k ^ h₁ →
    ∀ (m : ℕ) (g : Fin m → Fin (W p k)) (b : Fin m → Fin (2 ^ T₁))
      (code : Fin n → Fin m) (u' v' J' : Fin m → ℝ)
      (P' : Fin m → MvPolynomial (Fin 2) ℝ) (R : Fin n → Finset (Fin m)),
    Table p k G r ε T T₁ n γ j A u v P a e m g b code u' v' J' P' R →
    ENNReal.ofReal (N p k ^ (-σ)) ≤ pairMass p k T n γ j C u v P a e T₁ →
    Chart p B' r (L p) h₁ ε false k

end

end Submission.Obl.k4_scalar_pair_atlas_assembly
