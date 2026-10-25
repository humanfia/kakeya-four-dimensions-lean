-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/Interface.lean
import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_terminal_label_saturation

set_option linter.unusedVariables false

noncomputable def x : (ℕ × (Fin 6 → ℝ)) → ℝ → Fin 4 → ℝ :=
  fun l t => ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

noncomputable def y : (ℕ × (Fin 6 → ℝ)) → ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun l t => WithLp.toLp 2 ![(x l t) 1, (x l t) 2]

noncomputable def v : (ℕ × (Fin 6 → ℝ)) → EuclideanSpace ℝ (Fin 2) :=
  fun l => WithLp.toLp 2 ![l.2 3, l.2 4]

noncomputable def δ : ℝ → ℝ → ℝ :=
  fun N r => (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

noncomputable def obs : ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ :=
  fun B a p => (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2], ⌊B * (x p.1 p.2) 3 / a⌋)

noncomputable def fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  fun n H D A => ∃ m₀ : ℕ, (m₀ : ℝ) ≤ H ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin n) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ A ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true

noncomputable def prob : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℝ → ℝ → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ((k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) → ((k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal) → Prop :=
  fun N K L d S η W ω ν E P B f g G => (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧ 0 < L ∧ 0 < d ∧ d < 1 ∧ 0 < S ∧ 0 < η ∧ (fun μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) => (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (fmt 6 (N k ^ M) D (A j)) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (fmt 7 (N k ^ M) D ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}))) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k ∧ |MvPolynomial.eval (x l t) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(μ k γ), B k γ / K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) Set.univ) ∧ (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map (obs (B k γ) (δ (N k) r)) (μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) ∧ (∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧ MeasureTheory.Measure.map (fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) (μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) ∧ (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) ∧ (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | g k γ r ((obs (B k γ) (δ (N k) r)) p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((obs (B k γ) (δ (N k) r)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) ∧ (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) ∧ (∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c)))) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ))

noncomputable def chart : ℝ → ℕ → ℕ → ℝ → ℕ → ℝ → ℝ → ℝ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ → MvPolynomial (Fin 4) ℝ → Set (ℕ × (Fin 6 → ℝ)) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop → Prop :=
  fun Nk M D κ T j r Bv Ev c u Q R A F ex => Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧ R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Nk ^ M) ∧ MeasurableSet A ∧ MeasurableSet F ∧ (∀ i, fmt 6 (Nk ^ M) D {x | (i, x) ∈ A} ∧ fmt 7 (Nk ^ M) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) ∧ (∀ l ∈ A, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧ ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ ∧ |MvPolynomial.eval (x l t) R| ≤ κ * δ Nk r ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * Bv ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ κ * Bv ^ 2 / δ Nk r) ∧ (∀ p ∈ F, p ∈ Ev ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧ Bv / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) ∧ ex

end Submission.Obl.k4_terminal_label_saturation
