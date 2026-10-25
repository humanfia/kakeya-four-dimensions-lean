import Mathlib
import ChallengeDeps

-- Adapted from this LOT tree, o104, session x0350, commit 0e2b59568680:
-- Interface.lean and SplitInterfaces.lean (the latter from x0366 split 6dc6b23).
-- The definitions below name exactly the expressions in o115's frozen statement.

namespace Submission.Obl.k4_quadratic_atlas_normalization

noncomputable def x : (ℕ × (Fin 6 → ℝ)) → ℝ → Fin 4 → ℝ :=
  fun l t => ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

noncomputable def y : (ℕ × (Fin 6 → ℝ)) → ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun l t => WithLp.toLp 2 ![(x l t) 1, (x l t) 2]

noncomputable def δ : ℝ → ℝ → ℝ :=
  fun N r => (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

noncomputable def obs : ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ :=
  fun B a p => (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2], ⌊B * (x p.1 p.2) 3 / a⌋)

noncomputable def fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  fun n H D A => ∃ m₀ : ℕ, (m₀ : ℝ) ≤ H ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin n) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ A ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true

noncomputable def chart : ℝ → ℕ → ℕ → ℝ → ℕ → ℝ → ℝ → ℝ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ → MvPolynomial (Fin 4) ℝ → Set (ℕ × (Fin 6 → ℝ)) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop → Prop :=
  fun Nk M D κ T j r Bv Ev c u Q R A F ex => Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧ R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Nk ^ M) ∧ MeasurableSet A ∧ MeasurableSet F ∧ (∀ i, fmt 6 (Nk ^ M) D {x | (i, x) ∈ A} ∧ fmt 7 (Nk ^ M) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) ∧ (∀ l ∈ A, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧ ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ ∧ |MvPolynomial.eval (x l t) R| ≤ κ * δ Nk r ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * Bv ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ κ * Bv ^ 2 / δ Nk r) ∧ (∀ p ∈ F, p ∈ Ev ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧ Bv / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) ∧ ex

/-- The terminal extension assertion, with the model expressions named. -/

noncomputable def rough : ℝ → ℕ → ℕ → ℝ → ℕ → ℝ → ℝ → ℝ → ℝ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ → MvPolynomial (Fin 4) ℝ → Set (ℕ × (Fin 6 → ℝ)) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop → Prop :=
  fun Nk M D κ T j r a Bv Ev c u Q R A F ex => Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧ R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Nk ^ M) ∧ MeasurableSet A ∧ MeasurableSet F ∧ (∀ i, fmt 6 (Nk ^ M) D {x | (i, x) ∈ A} ∧ fmt 7 (Nk ^ M) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) ∧ (∀ l ∈ A, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧ ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ ∧ |MvPolynomial.eval (x l t) R| ≤ κ * δ Nk r * Nk ^ a ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * Bv * Nk ^ a ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ κ * Bv ^ 2 / δ Nk r) ∧ (∀ p ∈ F, p ∈ Ev ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)) ∧ (∀ l ∈ A, ∃ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T), Bv ^ 2 / (κ * Nk ^ a) ≤ |(MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)) ^ 2 - 2 * MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R)) * MvPolynomial.eval (x l t) (R)|) ∧ ex

noncomputable def knownSys : (ℕ → ℝ) → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → ℝ → ℝ → ℝ → Prop :=
  fun N W ω ν E B Lobs r h => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin C' → Fin (W k)) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')), (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ γ₁ o, ((lst γ₁ o).card : ℝ) ≤ κ) ∧ (∀ b, chart (N k) M D κ T ((j b : ℕ) : ℝ) r (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (∀ p ∈ F b, b ∈ lst (γ b) (obs (B k (γ b)) (δ (N k) Lobs) p))) ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod MeasureTheory.volume) (F b)

noncomputable def roughSys : (ℕ → ℝ) → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → ℝ → ℝ → ℝ → Prop :=
  fun N W ω ν E B L a h => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin C' → Fin (W k)) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')), (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ γ₁ o, ((lst γ₁ o).card : ℝ) ≤ κ) ∧ (∀ b, rough (N k) M D κ T ((j b : ℕ) : ℝ) L a (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (∀ p ∈ F b, b ∈ lst (γ b) (obs (B k (γ b)) (δ (N k) L) p))) ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod MeasureTheory.volume) (F b)

noncomputable def AtlasNormalization : Prop :=
  ∀ (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : (k : ℕ) → Fin (W k) → ℝ) (L a h : ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → 0 < L → 0 < a → 20 * a < L → (∀ k γ, 0 ≤ ω k γ) → (∀ k, (∑ γ, ω k γ) = 1) → (∀ k γ, MeasureTheory.IsProbabilityMeasure (ν k γ)) → (∃ Mb : ℕ, ∀ k γ, 0 < B k γ ∧ B k γ ≤ N k ^ Mb ∧ (B k γ)⁻¹ ≤ N k ^ Mb) → roughSys N W ω ν E B L a h → ∃ r : ℝ, 0 < r ∧ r < L ∧ L - r ≤ 20 * a ∧ knownSys N W ω ν E B L r h

end Submission.Obl.k4_quadratic_atlas_normalization
