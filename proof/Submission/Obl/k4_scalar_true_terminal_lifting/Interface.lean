import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces

/-!
# Interface for the true terminal lifting

The definitions of the frozen statement are those of
`Submission.Obl.k4_scalar_linear_critical_extremizers.Split` (o133), which are
definitionally the lambda-bound names of the frozen type.

* `RefBody` is the body of `Refinement` with all its witnesses explicit, so that
  `Refinement p q r b h ↔ ∃ φ ε B T γ j A C u v J P Λ θ, RefBody ...` is `Iff.rfl`.
* `BadWorldsSmall` is the terminal floor comparison: q-worlds whose parent
  assignment has `ν(A) < N ^ (f_q(L_q) - f_p(L_p) - δ) * J` carry power-small
  weighted q-mass.
* `LiftStatement` is the frozen statement in these names.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- The body of `Refinement p q r b h`, all witnesses explicit. -/
noncomputable def RefBody (p q : Code) (r b h : ℝ) (φ : ℕ → ℕ) (ε : ℕ → ℝ) (B : ℕ)
    (T : ℕ → ℕ)
    (γ : (k : ℕ) → Fin (W q k) → Fin (W p (φ k)))
    (j : (k : ℕ) → Fin (W q k) → Fin (2 ^ T k))
    (A : (k : ℕ) → Fin (W q k) → Set (ℕ × (Fin 5 → ℝ)))
    (C : (k : ℕ) → Fin (W q k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v J : (k : ℕ) → Fin (W q k) → ℝ)
    (P : (k : ℕ) → Fin (W q k) → MvPolynomial (Fin 2) ℝ)
    (Λ : (k : ℕ) → Fin (W p (φ k)) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W q k)))
    (θ : (k : ℕ) → Fin (W q k) → (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ))) : Prop :=
  (fun dt : ℕ → ℝ =>
    (fun t₀ : (k : ℕ) → Fin (W q k) → ℝ =>
    StrictMono φ ∧ (∀ k, 0 < ε k) ∧ Filter.Tendsto ε Filter.atTop (nhds 0) ∧ 1 ≤ B ∧
    (∀ k, N q k = N p (φ k) ∧
      ChartData p B r b (h + ε k) (ε k) false (φ k) (T k) (W q k)
        (γ k) (j k) (A k) (C k) (u k) (v k) (J k) (P k) (Λ k)) ∧
    (∀ k i, Measurable (θ k i) ∧ (∀ l, (θ k i l).1 = l.1) ∧
      (∀ l t, y (θ k i l) ((t - t₀ k i) / dt k) =
        (y l t - u k i - t * v k i) / J k i) ∧
      (∀ l t, x (θ k i l) ((t - t₀ k i) / dt k) =
        (x l t - MvPolynomial.eval ![t, y l t] (P k i)) / N p (φ k) ^ (-r)) ∧
      ν q k i = (ν p (φ k) (γ k i) (A k i))⁻¹ •
        MeasureTheory.Measure.map (θ k i) ((ν p (φ k) (γ k i)).restrict (A k i)) ∧
      mu q k i = (ENNReal.ofReal (dt k) * ν p (φ k) (γ k i) (A k i))⁻¹ •
        MeasureTheory.Measure.map (fun z => (θ k i z.1, (z.2 - t₀ k i) / dt k))
          ((mu p (φ k) (γ k i)).restrict (C k i))) ∧
    (∀ k, (fun Z : ℝ => 0 < Z ∧ ∀ i, ω q k i = (ω p (φ k) (γ k i) * dt k *
        (ν p (φ k) (γ k i) (A k i)).toReal) / Z)
      (∑ i : Fin (W q k), ω p (φ k) (γ k i) * dt k *
        (ν p (φ k) (γ k i) (A k i)).toReal)))
      (fun k i => (((j k i : Fin (2 ^ T k)) : ℕ) : ℝ) * dt k))
      (fun k => ((2 : ℝ) ^ T k)⁻¹)

theorem refinement_iff (p q : Code) (r b h : ℝ) :
    Refinement p q r b h ↔ ∃ φ ε B T γ j A C u v J P Λ θ,
      RefBody p q r b h φ ε B T γ j A C u v J P Λ θ := Iff.rfl

open Classical in
/-- The weighted q-mass of the q-worlds whose parent assignment is ratio-bad at
loss `δ`: `ν(A) < N ^ (f q (L q) - f p (L p) - δ) * J`. -/
noncomputable def badMass (p q : Code) (φ : ℕ → ℕ)
    (γ : (k : ℕ) → Fin (W q k) → Fin (W p (φ k)))
    (A : (k : ℕ) → Fin (W q k) → Set (ℕ × (Fin 5 → ℝ)))
    (J : (k : ℕ) → Fin (W q k) → ℝ) (δ : ℝ) (k : ℕ) : ENNReal :=
  ∑ i : Fin (W q k),
    if ν p (φ k) (γ k i) (A k i) <
        ENNReal.ofReal (N q k ^ (f q (L q) - f p (L p) - δ) * J k i) then
      ENNReal.ofReal (ω q k i) * mu q k i Set.univ
    else 0

/-- The terminal floor comparison (the density part of the lifting). -/
def BadWorldsSmall : Prop :=
  ∀ (p q : Code) (r b h : ℝ), Exact p → Exact q → 0 ≤ r → r < L p → r ≤ b →
    b ≤ L p → 0 ≤ h → L q = L p - r →
    ∀ φ ε B T γ j A C u v J P Λ θ, RefBody p q r b h φ ε B T γ j A C u v J P Λ θ →
    ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k in Filter.atTop, badMass p q φ γ A J δ k ≤ ENNReal.ofReal (N q k ^ (-c))

/-- The frozen statement, in the names of o133. -/
def LiftStatement : Prop :=
  ∀ (p q : Code) (r b h a : ℝ), Exact p → Exact q → 0 ≤ r → r < L p → r ≤ b →
    b ≤ L p → 0 ≤ h → L q = L p - r → Refinement p q r b h → Cost q a → Cost p (h + a)

end Submission.Obl.k4_scalar_true_terminal_lifting
