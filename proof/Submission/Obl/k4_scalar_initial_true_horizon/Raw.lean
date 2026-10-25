import Submission.Obl.k4_scalar_initial_true_horizon.Defs

/-! Raw true charts before terminal observation lists are installed. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

noncomputable def RawChartData : (p:Data) → ℕ → ℝ → ℝ → ℝ → ℝ → Bool → (k:ℕ) → (T n:ℕ) → (Fin n → Fin ((p).1 k)) → (Fin n → Fin (2 ^ T)) → (Fin n → Set (Trajectory)) → (Fin n → Set (Incidence)) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → MvPolynomial (Fin 2) ℝ) → Prop :=
  fun p B r b h ε isTrue k T n γ j A C u v J P => (2:ℝ) ^ T ≤ (N p) k ^ h∧(n:ℝ) ≤ (N p) k ^ (B:ℝ)∧(∀ i,MeasurableSet (A i)∧MeasurableSet (C i))∧(∀ i i',i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))∧(∀ i,C i ⊆ (event p) k (γ i) ∩ (A i ×ˢ I T (j i)))∧(∀ i,0 < mu p k (γ i) (C i)∧0 < J i∧(J i)⁻¹ ≤ (N p) k ^ (B:ℝ)∧J i ≤ (N p) k ^ ε / (2:ℝ) ^ T∧|u i| + |v i| ≤ (N p) k ^ ε∧(P i).totalDegree ≤ 2∧(∀ a,|(P i).coeff a| ≤ (N p) k ^ (B:ℝ))∧(∀ l ∈ A i,(l.1:ℝ) ≤ (N p) k ^ (B:ℝ)∧∀ e,|l.2 e| ≤ (N p) k ^ ε)∧(∀ z:ℕ,Format 5 ((N p) k ^ (B:ℝ)) B {a | (z,a) ∈ A i})∧(∀ z:ℕ,Format 6 ((N p) k ^ (B:ℝ)) B {a | ((z,fun e:Fin 5 => a e.castSucc),a 5) ∈ C i})∧(∀ l ∈ A i,∀ t ∈ I T (j i),|y l t - u i - t * v i| ≤ (N p) k ^ ε * J i∧|x l t - MvPolynomial.eval ![t,y l t] (P i)| ≤ (N p) k ^ ε * (N p) k ^ (-r))∧(isTrue = true → ENNReal.ofReal ((N p) k ^ (-(profile p) r) * J i / ((N p) k ^ ε * (2:ℝ) ^ T)) ≤ mu p k (γ i) (C i)))∧ENNReal.ofReal ((N p) k ^ (-ε)) ≤ ∑ a:Fin ((p).1 k),ENNReal.ofReal ((weight p) k a) * mu p k a {q | ∃ i,γ i = a∧q ∈ C i}

noncomputable def RawChart (p : Data) (B : ℕ) (r b h ε : ℝ) (isTrue : Bool) (k : ℕ) : Prop :=
  ∃ (T n : ℕ) (γ : Fin n → Fin (worlds p k)) (j : Fin n → Fin (2 ^ T))
    (A : Fin n → Set Trajectory) (C : Fin n → Set Incidence)
    (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ),
    RawChartData p B r b h ε isTrue k T n γ j A C u v J P

end Submission.Obl.k4_scalar_initial_true_horizon
