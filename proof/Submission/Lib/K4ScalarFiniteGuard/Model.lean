/-
Adapted from: here:o093
Original proofs by session x0535 in this LOT workspace. The scalar atlas
interface was written in the same o093 tree by x0364; this package retains
its literal fields while requiring only the sampling hypotheses used here.
-/

import Mathlib

set_option autoImplicit false

namespace Submission.Lib.K4ScalarFiniteGuard

open MeasureTheory Filter
open scoped Topology

/-- Data used by the scalar known-atlas interface. No exact-profile,
probability or chart-calculus assertion is hidden in this carrier. -/
structure Model where
  worlds : ℕ → ℕ
  resolution : ℕ → ℝ
  length : ℝ
  weights : (k : ℕ) → Fin (worlds k) → ℝ
  priors : (k : ℕ) → Fin (worlds k) → Measure (ℕ × (Fin 5 → ℝ))
  events : (k : ℕ) → Fin (worlds k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)
  profile : ℝ → ℝ

abbrev Code := Model
noncomputable def W (p : Code) : ℕ → ℕ := p.worlds
noncomputable def N (p : Code) : ℕ → ℝ := p.resolution
noncomputable def L (p : Code) : ℝ := p.length
noncomputable def ω (p : Code) : (k : ℕ) → Fin (W p k) → ℝ := p.weights
noncomputable def ν (p : Code) : (k : ℕ) → Fin (W p k) → Measure (ℕ × (Fin 5 → ℝ)) := p.priors
noncomputable def E (p : Code) : (k : ℕ) → Fin (W p k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ) := p.events
noncomputable def f (p : Code) : ℝ → ℝ := p.profile
noncomputable def mu (p : Code) (k : ℕ) (a : Fin (W p k)) :
    Measure ((ℕ × (Fin 5 → ℝ)) × ℝ) := ((ν p k a).prod volume).restrict (E p k a)

/-- The only assumptions on the original sequence needed for chart
transport and the compact finite-sample guard. -/
def Sampling (p : Code) : Prop := (∀ k, 2 ≤ N p k) ∧ Tendsto (N p) atTop atTop

noncomputable def y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ :=
  fun l t => l.2 0 + t * l.2 1

noncomputable def x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ :=
  fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

noncomputable def I : (T : ℕ) → Fin (2 ^ T) → Set ℝ :=
  fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

noncomputable def Format : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  fun n B D A => ∃ k : ℕ, (k : ℝ) ≤ B ∧ ∃ p : Fin k → MvPolynomial (Fin n) ℝ, (∀ j, (p j).totalDegree ≤ D ∧ ∀ b, |(p j).coeff b| ≤ B) ∧ ∃ S : Set (Fin k → SignType), A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S}

/-! The literal hypotheses of the frozen scalar exact sequence. -/

noncomputable def ChartData : (p : Code) → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → (k : ℕ) →
    (T n : ℕ) → (Fin n → Fin (W p k)) → (Fin n → Fin (2 ^ T)) →
    (Fin n → Set (ℕ × (Fin 5 → ℝ))) → (Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) →
    (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (Fin n → MvPolynomial (Fin 2) ℝ) →
    (Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)) → Prop :=
  fun p B r b h ε isTrue k T n γ j A C u v J P Λ =>
    (2 : ℝ) ^ T ≤ N p k ^ h ∧
    (n : ℝ) ≤ N p k ^ (B : ℝ) ∧
    (∀ i, MeasurableSet (A i) ∧ MeasurableSet (C i)) ∧
    (∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) ∧
    (∀ i, C i ⊆ E p k (γ i) ∩ (A i ×ˢ I T (j i))) ∧
    (∀ i, 0 < mu p k (γ i) (C i) ∧ 0 < J i ∧ (J i)⁻¹ ≤ N p k ^ (B : ℝ) ∧
      J i ≤ N p k ^ ε / (2 : ℝ) ^ T ∧ |u i| + |v i| ≤ N p k ^ ε ∧
      (P i).totalDegree ≤ 2 ∧ (∀ a, |(P i).coeff a| ≤ N p k ^ (B : ℝ)) ∧
      (∀ l ∈ A i, (l.1 : ℝ) ≤ N p k ^ (B : ℝ) ∧ ∀ e, |l.2 e| ≤ N p k ^ ε) ∧
      (∀ z : ℕ, Format 5 (N p k ^ (B : ℝ)) B {a | (z, a) ∈ A i}) ∧
      (∀ z : ℕ, Format 6 (N p k ^ (B : ℝ)) B
        {a | ((z, fun e : Fin 5 => a e.castSucc), a 5) ∈ C i}) ∧
      (∀ l ∈ A i, ∀ t ∈ I T (j i),
        |y l t - u i - t * v i| ≤ N p k ^ ε * J i ∧
        |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N p k ^ ε * N p k ^ (-r)) ∧
      (isTrue = true → ENNReal.ofReal (N p k ^ (-f p r) * J i /
        (N p k ^ ε * (2 : ℝ) ^ T)) ≤ mu p k (γ i) (C i))) ∧
    (∀ a z, ((Λ a z).card : ℝ) ≤ N p k ^ ε) ∧
    (∀ a i, MeasurableSet {z | i ∈ Λ a z}) ∧
    (∀ i, mu p k (γ i) {q | q ∈ C i ∧
      i ∉ Λ (γ i) ((![q.2, y q.1 q.2] : Fin 2 → ℝ),
        (⌊x q.1 q.2 / (N p k ^ (-b))⌋ : ℤ))} = 0) ∧
    ENNReal.ofReal (N p k ^ (-ε)) ≤ ∑ a : Fin (W p k),
      ENNReal.ofReal (ω p k a) * mu p k a {q | ∃ i, γ i = a ∧ q ∈ C i}

/-! A scalar chart system, including selected incidences, tempered assignments and terminal-observation lists. The Boolean adds true floors. -/

noncomputable def Chart : Code → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → ℕ → Prop :=
  fun p B r b h ε isTrue k =>
  ∃ (T n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
    (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)),
    ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ

noncomputable def Known : Code → ℝ → ℝ → ℝ → Prop :=
  fun p r b h => 0 ≤ h ∧ ∃ B : ℕ, 1 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, Chart p B r b (h + ε) ε false k

end Submission.Lib.K4ScalarFiniteGuard
