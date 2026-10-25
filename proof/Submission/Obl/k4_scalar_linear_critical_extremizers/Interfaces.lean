/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/Interfaces.lean.
-/

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_linear_critical_extremizers.Split

open MeasureTheory Filter

noncomputable def TCM : Prop :=
  (∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) → (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) → (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) → (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) → (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) → (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) → ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0)

noncomputable def STI : Prop :=
  (∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ S : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < S → ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ) (T n : ℕ → ℝ → ℕ) (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ))) (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ), (fun (y x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun z : ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 2 → ℤ => (∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1 ∧ (∀ g, MeasureTheory.IsProbabilityMeasure (ν k g) ∧ MeasureTheory.IsProbabilityMeasure (π k g) ∧ (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧ ρ k g ≤ ENNReal.ofReal (K k) • ((ν k g).prod MeasureTheory.volume) ∧ ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (W k)) (r s b : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∀ c : ℤ, π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-S * b))) ∧ (∀ (q : Fin 2 → ℤ) (a : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s))) ∧ (∀ (q : Fin 2 → ℤ) (a c : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a ∧ (⌊p.1.2 1 / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) * π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i)) ∧ (∀ i i', i ≠ i' → γ k s i = γ k s i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (N k ^ (-d * s) / (K k * (2 : ℝ) ^ T k s)) ≤ ν k (γ k s i) (A k s i) ∧ ν k (γ k s i) (A k s i) ≤ ENNReal.ofReal (K k * N k ^ (-d * s) / (2 : ℝ) ^ T k s) ∧ ENNReal.ofReal ((K k * (2 : ℝ) ^ T k s)⁻¹) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) (A k s i ×ˢ I (T k s) (j k s i)) ∧ |u k s i| + |v k s i| ≤ K k ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ t ∈ I (T k s) (j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2, |MvPolynomial.eval ![t, u k s i + t * v k s i + w / (2 : ℝ) ^ T k s] (F k s i)| ≤ K k) ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |y l t - u k s i - t * v k s i| ≤ K k / (2 : ℝ) ^ T k s ∧ |x l t - MvPolynomial.eval ![t, y l t] (F k s i)| ≤ K k * N k ^ (-s))) ∧ (∀ g : Fin (W k), ρ k g {p | ∃ i, γ k s i = g ∧ p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i)}ᶜ = 0)) → ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ (s c : ℝ) (i : Fin (n k s)) (P : MvPolynomial (Fin 2) ℝ), R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ c ∧ c ≤ R ∧ P.totalDegree ≤ 2 ∧ (∀ b, |P.coeff b| ≤ N k ^ R) ∧ ENNReal.ofReal (N k ^ (-d * c - ε) / (2 : ℝ) ^ T k s) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) {p | p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i) ∧ ∀ t ∈ I (T k s) (j k s i), |x p.1 t - MvPolynomial.eval ![t, y p.1 t] P| ≤ N k ^ ε * N k ^ (-s - c)}) (fun B r p e => ⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / (B ^ (-r))⌋)) (fun l t => l.2 0 + t * l.2 1) (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)))

/-! Mathlib-only carrier of scalar exact sequence data; W is the dependent index. -/
noncomputable def Code : Type :=
  Σ W : ℕ → ℕ, (ℕ → ℝ) × (ℕ → ℝ) × ℕ × ℕ × ℝ × ℝ × ℝ × ℝ × ((k : ℕ) → Fin (W k) → ℝ) × ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) × ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) × ((k : ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal) × ((k : ℕ) → Fin (W k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal) × (ℝ → ℝ)

noncomputable def W : Code → ℕ → ℕ :=
  fun p => p.1

noncomputable def N : Code → ℕ → ℝ :=
  fun p => p.2.1

noncomputable def K : Code → ℕ → ℝ :=
  fun p => p.2.2.1

noncomputable def M : Code → ℕ :=
  fun p => p.2.2.2.1

noncomputable def D : Code → ℕ :=
  fun p => p.2.2.2.2.1

noncomputable def L : Code → ℝ :=
  fun p => p.2.2.2.2.2.1

noncomputable def d : Code → ℝ :=
  fun p => p.2.2.2.2.2.2.1

noncomputable def S : Code → ℝ :=
  fun p => p.2.2.2.2.2.2.2.1

noncomputable def U : Code → ℝ :=
  fun p => p.2.2.2.2.2.2.2.2.1

noncomputable def ω : (p : Code) → (k : ℕ) → Fin (W p k) → ℝ :=
  fun p => p.2.2.2.2.2.2.2.2.2.1

noncomputable def ν : (p : Code) → (k : ℕ) → Fin (W p k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ)) :=
  fun p => p.2.2.2.2.2.2.2.2.2.2.1

noncomputable def E : (p : Code) → (k : ℕ) → Fin (W p k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  fun p => p.2.2.2.2.2.2.2.2.2.2.2.1

noncomputable def g : (p : Code) → (k : ℕ) → Fin (W p k) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal :=
  fun p => p.2.2.2.2.2.2.2.2.2.2.2.2.1

noncomputable def G : (p : Code) → (k : ℕ) → Fin (W p k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal :=
  fun p => p.2.2.2.2.2.2.2.2.2.2.2.2.2.1

noncomputable def f : Code → ℝ → ℝ :=
  fun p => p.2.2.2.2.2.2.2.2.2.2.2.2.2.2

noncomputable def mu : (p : Code) → (k : ℕ) → Fin (W p k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  fun p k a => ((ν p k a).prod MeasureTheory.volume).restrict (E p k a)

noncomputable def y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ :=
  fun l t => l.2 0 + t * l.2 1

noncomputable def x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ :=
  fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

noncomputable def I : (T : ℕ) → Fin (2 ^ T) → Set ℝ :=
  fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

noncomputable def Format : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  fun n B D A => ∃ k : ℕ, (k : ℝ) ≤ B ∧ ∃ p : Fin k → MvPolynomial (Fin n) ℝ, (∀ j, (p j).totalDegree ≤ D ∧ ∀ b, |(p j).coeff b| ≤ B) ∧ ∃ S : Set (Fin k → SignType), A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S}

/-! The literal hypotheses of the frozen scalar exact sequence. -/
noncomputable def Exact : Code → Prop :=
  fun edc => ((∀ k, 2 ≤ (N edc) k) ∧ Filter.Tendsto (N edc) Filter.atTop Filter.atTop ∧
    ((∀ k, 1 ≤ (K edc) k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, (K edc) k ≤ (N edc) k ^ ε) ∧
    1 ≤ (M edc) ∧ 1 ≤ (D edc) ∧ 0 < (L edc) ∧ 0 ≤ (d edc) ∧ (d edc) < 1 ∧ 0 < (S edc) ∧ 0 < (U edc)) ∧
    ((∀ k, ((W edc) k : ℝ) ≤ (N edc) k ^ ((M edc) : ℝ) ∧ (∀ γ, 0 ≤ (ω edc) k γ) ∧ (∑ γ, (ω edc) k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure ((ν edc) k γ) ∧ (∃ n : ℕ, (n : ℝ) ≤ (N edc) k ^ ((M edc) : ℝ) ∧ ∃ (h : Fin n → ℝ) (i : Fin n → ℕ) (B : Fin n → Set (Fin 5 → ℝ)), (∀ j, 0 ≤ h j ∧ h j ≤ (N edc) k ^ ((M edc) : ℝ) ∧ (i j : ℝ) ≤ (N edc) k ^ ((M edc) : ℝ) ∧ Format 5 ((N edc) k ^ ((M edc) : ℝ)) (D edc) (B j) ∧ (∀ b ∈ B j, ∀ e, |b e| ≤ (N edc) k ^ ((M edc) : ℝ))) ∧ (ν edc) k γ = ∑ j, ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j, b)) (MeasureTheory.volume.restrict (B j))) ∧ (∀ᵐ l ∂(ν edc) k γ, ∀ e, |l.2 e| ≤ (K edc) k) ∧ MeasurableSet ((E edc) k γ) ∧ (E edc) k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ (E edc) k γ, (p.1.1 : ℝ) ≤ (N edc) k ^ ((M edc) : ℝ)) ∧ (∀ i : ℕ, Format 6 ((N edc) k ^ ((M edc) : ℝ)) (D edc) {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ (E edc) k γ})) ∧ ENNReal.ofReal (((K edc) k)⁻¹) ≤ ∑ γ, ENNReal.ofReal ((ω edc) k γ) * (mu edc) k γ Set.univ)) ∧
    ((∀ k γ r, 0 ≤ r → r ≤ (L edc) → Measurable ((g edc) k γ r) ∧ MeasureTheory.Measure.map (fun p => ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋ : ℤ))) ((mu edc) k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity ((g edc) k γ r))) ∧
    ((∀ k γ u, 0 < u → u ≤ (U edc) → Measurable ((G edc) k γ u) ∧ MeasureTheory.Measure.map (fun p => (((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / ((N edc) k ^ (-(L edc)))⌋ : ℤ)), (⌊p.1.2 1 / ((N edc) k ^ (-u))⌋ : ℤ))) ((mu edc) k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity ((G edc) k γ u))) ∧
    ((∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ (L edc) → 0 ≤ (f edc) s - (f edc) r ∧ (f edc) s - (f edc) r ≤ s - r)) ∧
    ((∀ r τ : ℝ, 0 ≤ r → r ≤ (L edc) → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal ((ω edc) k γ) * (mu edc) k γ {p | (g edc) k γ r ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋ : ℤ)) < ENNReal.ofReal ((N edc) k ^ (-(f edc) r - τ)) ∨ ENNReal.ofReal ((N edc) k ^ (-(f edc) r + τ)) < (g edc) k γ r ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / ((N edc) k ^ (-r))⌋ : ℤ))}) ≤ ENNReal.ofReal ((N edc) k ^ (-c)))) ∧
    ((∀ r : ℝ, 0 ≤ r → r ≤ (L edc) → (f edc) (L edc) - (f edc) r ≤ (d edc) * ((L edc) - r))) ∧
    ((∀ u τ : ℝ, 0 < u → u ≤ (U edc) → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal ((ω edc) k γ) * (mu edc) k γ {p | ENNReal.ofReal ((N edc) k ^ (-(f edc) (L edc) - (S edc) * u + τ)) < (G edc) k γ u (((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / ((N edc) k ^ (-(L edc)))⌋ : ℤ)), (⌊p.1.2 1 / ((N edc) k ^ (-u))⌋ : ℤ))}) ≤ ENNReal.ofReal ((N edc) k ^ (-c))))

/-! The explicit data predicate of a tempered scalar atlas. C records selected incidences; A always retains the full assigned prior. -/
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

noncomputable def Cost : Code → ℝ → Prop :=
  fun p h => 0 ≤ h ∧ ∃ B : ℕ, 1 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, Chart p B (L p) (L p) (h + ε) ε true k

noncomputable def Horizon : Code → ℝ :=
  fun p => sInf {h : ℝ | Cost p h}

/-! Scalar initial true horizon, with tempered lists and assignments. -/
noncomputable def Initial : Prop :=
  ∀ p : Code, Exact p → Cost p (L p)

/-! An actual normalized sequence: a chosen atlas subsequence, whole assigned conditional priors, selected-law pushforwards, and original mixture weights. Time and scalar residual coordinate identities hold for entire trajectories. -/
noncomputable def Refinement : Code → Code → ℝ → ℝ → ℝ → Prop :=
  fun p q r b h =>
    ∃ (φ : ℕ → ℕ) (ε : ℕ → ℝ) (B : ℕ) (T : ℕ → ℕ)
      (γ : (k : ℕ) → Fin (W q k) → Fin (W p (φ k)))
      (j : (k : ℕ) → Fin (W q k) → Fin (2 ^ T k))
      (A : (k : ℕ) → Fin (W q k) → Set (ℕ × (Fin 5 → ℝ)))
      (C : (k : ℕ) → Fin (W q k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
      (u v J : (k : ℕ) → Fin (W q k) → ℝ)
      (P : (k : ℕ) → Fin (W q k) → MvPolynomial (Fin 2) ℝ)
      (Λ : (k : ℕ) → Fin (W p (φ k)) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W q k)))
      (θ : (k : ℕ) → Fin (W q k) → (ℕ × (Fin 5 → ℝ)) → (ℕ × (Fin 5 → ℝ))),
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

/-! Scaling, coarsening and normalization with horizon composition. All cap parameters and relative profiles are explicit. -/
noncomputable def Calculus : Prop :=
  (∀ (p : Code) (α : ℝ), Exact p → 0 < α →
    ∃ q : Code, Exact q ∧ L q = L p / α ∧ d q = d p ∧ S q = S p ∧ U q = U p / α ∧
      Horizon q = Horizon p / α ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ L q → f q r - f q 0 = (f p (α * r) - f p 0) / α) ∧
  (∀ (p : Code) (r d' : ℝ), Exact p → 0 < r → r < L p → 0 ≤ d' → d' < 1 →
    (∀ s : ℝ, 0 ≤ s → s ≤ r → f p r - f p s ≤ d' * (r - s)) →
    ∃ q : Code, Exact q ∧ L q = r ∧ d q = d' ∧ S q = S p ∧
      U q = U p * r / L p ∧ (∀ s : ℝ, 0 ≤ s → s ≤ r → f q s - f q 0 = f p s - f p 0) ∧
      (∀ h : ℝ, Cost q h → Known p r r h)) ∧
  (∀ (p : Code) (r b h d' : ℝ), Exact p → 0 ≤ r → r < L p →
    r ≤ b → b ≤ L p → 0 ≤ d' → d' < 1 →
    (∀ s : ℝ, r ≤ s → s ≤ L p → f p (L p) - f p s ≤ d' * (L p - s)) →
    Known p r b h → ∃ q : Code, Exact q ∧ L q = L p - r ∧ d q = d' ∧ S q = S p ∧
      U q = U p * (L p - r) / L p ∧ Refinement p q r b h ∧ Horizon p ≤ h + Horizon q ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ L q →
        f q (L q) - f q s ≤ f p (L p) - f p (r + s)) ∧
      (b = r → ∀ s : ℝ, 0 ≤ s → s ≤ L q → f q s - f q 0 = f p (r + s) - f p r))

/-! Uniform scalar terminal time extension. C and c precede and are independent of the exact data and their complexity. -/
noncomputable def Extension : Prop :=
  ∀ d₀ S₀ η : ℝ, 0 ≤ d₀ → d₀ < 1 → 0 < S₀ → 0 < η →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ p : Code, Exact p → d p ≤ d₀ → S p = S₀ →
      U p = η * L p → ∀ h e : ℝ, 0 < h → Cost p h → 0 < e → e < h → e < c * L p →
      ∃ r : ℝ, 0 < r ∧ r < L p ∧ L p - r ≤ C * e ∧ Known p r (L p) (h - e)

/-! The numerical part of chart calculus used to select extremizers; actual transports are retained in Calculus for the tangent child. -/
noncomputable def WeakCalculus : Prop :=
  (∀ (p : Code) (α : ℝ), Exact p → 0 < α →
    ∃ q : Code, Exact q ∧ L q = L p / α ∧ d q = d p ∧ S q = S p ∧ U q = U p / α ∧
      Horizon q = Horizon p / α ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ L q → f q r - f q 0 = (f p (α * r) - f p 0) / α) ∧
  (∀ (p : Code) (r d' : ℝ), Exact p → 0 < r → r < L p → 0 ≤ d' → d' < 1 →
    (∀ s : ℝ, 0 ≤ s → s ≤ r → f p r - f p s ≤ d' * (r - s)) →
    ∃ q : Code, Exact q ∧ L q = r ∧ d q = d' ∧ S q = S p ∧
      U q = U p * r / L p ∧ (∀ s : ℝ, 0 ≤ s → s ≤ r → f q s - f q 0 = f p s - f p 0) ∧
      (∀ h : ℝ, Cost q h → Known p r r h)) ∧
  (∀ (p : Code) (r b h d' : ℝ), Exact p → 0 ≤ r → r < L p →
    r ≤ b → b ≤ L p → 0 ≤ d' → d' < 1 →
    (∀ s : ℝ, r ≤ s → s ≤ L p → f p (L p) - f p s ≤ d' * (L p - s)) →
    Known p r b h → ∃ q : Code, Exact q ∧ L q = L p - r ∧ d q = d' ∧ S q = S p ∧
      U q = U p * (L p - r) / L p ∧ Horizon p ≤ h + Horizon q ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ L q →
        f q (L q) - f q s ≤ f p (L p) - f p (r + s)) ∧
      (b = r → ∀ s : ℝ, 0 ≤ s → s ≤ L q → f q s - f q 0 = f p (r + s) - f p r))

/-! Linear relative-profile maximizing exact problems, with global comparison rates in the same angular class and a buffer above d_*; no tangent limit preserves horizon by fiat. -/
noncomputable def Critical : Prop :=
  ∃ S₀ η d₀ κ : ℝ, ∃ p : ℕ → Code, ∃ D₀ b : ℕ → ℝ,
    0 < S₀ ∧ 0 < η ∧ 0 ≤ d₀ ∧ d₀ < 1 ∧ 0 < κ ∧ κ ≤ 1 ∧
    (∀ i, Exact (p i) ∧ L (p i) = 1 ∧ S (p i) = S₀ ∧ U (p i) = η ∧
      d (p i) ≤ D₀ i ∧ d₀ < D₀ i ∧ D₀ i < 1 ∧ 0 ≤ b i ∧ b i ≤ 1) ∧
    Filter.Tendsto (fun i => d (p i)) Filter.atTop (nhds d₀) ∧
    Filter.Tendsto D₀ Filter.atTop (nhds d₀) ∧
    Filter.Tendsto b Filter.atTop (nhds κ) ∧
    Filter.Tendsto (fun i => Horizon (p i)) Filter.atTop (nhds κ) ∧
    (∀ i q, Exact q → d q ≤ D₀ i → S q = S₀ → U q = η * L q →
      Horizon q ≤ b i * L q) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ i in Filter.atTop, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      |f (p i) r - f (p i) 0 - d₀ * r| ≤ ε * (D₀ i - d₀))

end Submission.Obl.k4_scalar_linear_critical_extremizers.Split
