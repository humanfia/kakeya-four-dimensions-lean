import Mathlib
import ChallengeDeps

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_general_parent_wide_layer_candidates.Split

def RawComparisonStatement : Prop :=
∀ (α : Type) [MeasurableSpace α] (N K : ℕ → ℝ) (d κ ℓ S U e₀ : ℝ)
  (ν : ℕ → MeasureTheory.Measure α) (μ ρ : ℕ → MeasureTheory.Measure (α × ℝ))
  (π : ℕ → MeasureTheory.Measure ℝ) (b : ℕ → α → Fin 6 → ℝ)
  (P : ℕ → MvPolynomial (Fin 4) ℝ) (T n : ℕ → ℝ → ℕ)
  (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
  (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α)
  (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ)
  (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ),
(fun (x : ℕ → α → ℝ → Fin 4 → ℝ) =>
(fun (block : (T : ℕ) → Fin (2 ^ T) → Set ℝ) =>
(fun (z : ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ) =>
(fun (fit : ℕ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → α → Set ℝ → Prop) =>
(fun (basic : Prop) =>
(fun (caps : Prop) =>
(fun (atDepth : ℕ → ℝ → ℝ → Prop) =>
(fun (prepared : Prop) =>
(fun (nested : Prop) =>
(fun (valid : Prop) =>
(fun (lex : ℝ → ℝ → ℝ → Prop) =>
(fun (wide : Prop) =>
(fun (bgood : ℕ → Set (α × ℝ)) =>
(fun (mcode : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℤ × ℤ × ℤ) =>
(fun (dcode : ℕ → ℝ → ℝ → ℝ → (α × ℝ) → ℤ × ℤ × ℤ) =>
(fun (fib : (k : ℕ) → (r m H : ℝ) → Fin (n k r) → (Fin 2 → ℤ) → Set (Fin 3 → ℝ)) =>
(fun (ce : ℝ → ℝ → ℝ → ℝ → Prop) =>
(fun (layerValid : ∀ (k : ℕ) (s m H beta : ℝ) (nn : ℕ) (sets : Fin nn → Set α) (tag : Fin nn → Fin 2 → ℤ) (center velocity : Fin nn → ℝ) (poly : Fin nn → MvPolynomial (Fin 2) ℝ), Prop) =>
(fun (cc : ∀ (k : ℕ) (r u v m H : ℝ) (beta : Fin 3 → ℝ)
    (pn : Fin 3 → ℕ)
    (pC : (a : Fin 3) → Fin (pn a) → Set α)
    (pTag : (a : Fin 3) → Fin (pn a) → Fin 2 → ℤ)
    (pU : (a : Fin 3) → Fin (pn a) → ℝ)
    (pV : (a : Fin 3) → Fin (pn a) → ℝ)
    (pG : (a : Fin 3) → Fin (pn a) → MvPolynomial (Fin 2) ℝ)
    (lam : MeasureTheory.Measure (α × ℝ))
    (cnt : Fin 2 → ℕ)
    (par : ∀ a, Fin (cnt a) → Fin (n k r))
    (co : ∀ a, Fin (cnt a) → Fin (pn 0))
    (fi : ∀ a, Fin (cnt a) → Fin (pn a.succ))
    (dom : ∀ a, Fin (cnt a) → ℤ × ℤ × ℤ)
    (ev : ∀ a, Fin (cnt a) → Set (α × ℝ))
    (cs : Fin (n k r) → (Fin 2 → ℤ) → Finset (Fin (pn 0)))
    (fs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) →
    Finset (Fin (pn a.succ)))
    (ofs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) → Fin (pn a.succ) → ℝ), Prop) =>
(fun (samples : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) =>
(∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
    ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
      (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)),
      (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) →
      (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) →
      (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) →
      (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv j (f₁ i) t| ≤ N ^ η) →
      (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv j (f₂ i) t| ≤ N ^ η) →
      (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) →
      (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 →
      MeasureTheory.IsProbabilityMeasure μ →
      (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) →
      (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) →
      ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧
          N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0) → valid → wide → ∀ Ucap : ℝ, 0 < Ucap → ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ r u v m : ℝ, ce r u v m ∧ m ≤ Ucap ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, ∃ H : ℝ, 2 ≤ H ∧ K (τ k) ≤ H ∧ H ≤ N (τ k) ^ ε ∧ samples (τ k) r u v m H) (fun k r u v m H => ∃ (beta : Fin 3 → ℝ)
    (pn : Fin 3 → ℕ)
    (pC : (a : Fin 3) → Fin (pn a) → Set α)
    (pTag : (a : Fin 3) → Fin (pn a) → Fin 2 → ℤ)
    (pU : (a : Fin 3) → Fin (pn a) → ℝ)
    (pV : (a : Fin 3) → Fin (pn a) → ℝ)
    (pG : (a : Fin 3) → Fin (pn a) → MvPolynomial (Fin 2) ℝ)
    (lam : MeasureTheory.Measure (α × ℝ))
    (cnt : Fin 2 → ℕ)
    (par : ∀ a, Fin (cnt a) → Fin (n k r))
    (co : ∀ a, Fin (cnt a) → Fin (pn 0))
    (fi : ∀ a, Fin (cnt a) → Fin (pn a.succ))
    (dom : ∀ a, Fin (cnt a) → ℤ × ℤ × ℤ)
    (ev : ∀ a, Fin (cnt a) → Set (α × ℝ))
    (cs : Fin (n k r) → (Fin 2 → ℤ) → Finset (Fin (pn 0)))
    (fs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) →
    Finset (Fin (pn a.succ)))
    (ofs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) → Fin (pn a.succ) → ℝ), cc k r u v m H beta pn pC pTag pU pV pG lam cnt par co fi dom ev cs fs ofs)) (fun (k : ℕ) (r u v m H : ℝ) (beta : Fin 3 → ℝ)
    (pn : Fin 3 → ℕ)
    (pC : (a : Fin 3) → Fin (pn a) → Set α)
    (pTag : (a : Fin 3) → Fin (pn a) → Fin 2 → ℤ)
    (pU : (a : Fin 3) → Fin (pn a) → ℝ)
    (pV : (a : Fin 3) → Fin (pn a) → ℝ)
    (pG : (a : Fin 3) → Fin (pn a) → MvPolynomial (Fin 2) ℝ)
    (lam : MeasureTheory.Measure (α × ℝ))
    (cnt : Fin 2 → ℕ)
    (par : ∀ a, Fin (cnt a) → Fin (n k r))
    (co : ∀ a, Fin (cnt a) → Fin (pn 0))
    (fi : ∀ a, Fin (cnt a) → Fin (pn a.succ))
    (dom : ∀ a, Fin (cnt a) → ℤ × ℤ × ℤ)
    (ev : ∀ a, Fin (cnt a) → Set (α × ℝ))
    (cs : Fin (n k r) → (Fin 2 → ℤ) → Finset (Fin (pn 0)))
    (fs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) →
    Finset (Fin (pn a.succ)))
    (ofs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) → Fin (pn a.succ) → ℝ) => (2 ≤ H) ∧
  (∀ a, layerValid k (![r, r + u, r + v] a) m H (beta a) (pn a) (pC a) (pTag a) (pU a) (pV a) (pG a)) ∧
  (∀ a i e, |((pG a) i).coeff e| ≤ N k ^ (m / 1000)) ∧
  (lam ≤ ρ k) ∧
  (ENNReal.ofReal H⁻¹ ≤ lam Set.univ) ∧
  (∀ a e, MeasurableSet (ev a e)) ∧
  (∀ a, Pairwise (fun e f => Disjoint (ev a e) (ev a f))) ∧
  (∀ a, ∀ᵐ ω ∂lam, ∃ e, ω ∈ ev a e) ∧
  (∀ a, Function.Injective
    (fun e => (par a e, co a e, fi a e, dom a e))) ∧
  (∀ a e ω, ω ∈ ev a e →
    ω ∈ bgood k ∧ ω.1 ∈ B k r (par a e) ∧
      ω.2 ∈ block (T k r) (j k r (par a e)) ∧
      ω.1 ∈ (pC 0) (co a e) ∧ ω.1 ∈ (pC a.succ) (fi a e) ∧
      dcode k ((2 : ℝ) ^ (-(T k r : ℤ))) (N k ^ (-ℓ * r))
        ((2 : ℝ) ^ (-(T k r : ℤ)) * N k ^ (-ℓ * r)) ω = dom a e) ∧
  (∀ a e,
    0 < π k {w : ℝ | ⌊w / N k ^ (-m)⌋ = (pTag 0) (co a e) 0}) ∧
  (∀ a e,
    ENNReal.ofReal (((2 : ℝ) ^ (-(T k r : ℤ))) * N k ^ (-m) *
      (((2 : ℝ) ^ (-(T k r : ℤ))) * N k ^ (-ℓ * r)) *
      (N k ^ (-r - ![u, v] a)) ^ d / H) *
      π k {w : ℝ | ⌊w / N k ^ (-m)⌋ = (pTag 0) (co a e) 0} ≤ lam (ev a e)) ∧
  (∀ a,
    (∑ e, ENNReal.ofReal (((2 : ℝ) ^ (-(T k r : ℤ))) * N k ^ (-m) *
      (((2 : ℝ) ^ (-(T k r : ℤ))) * N k ^ (-ℓ * r)) *
      (N k ^ (-r - ![u, v] a)) ^ d) *
      π k {w : ℝ | ⌊w / N k ^ (-m)⌋ = (pTag 0) (co a e) 0}) ≤ ENNReal.ofReal H) ∧
  (∀ Q tag, ((cs Q tag).card : ℝ) ≤ H ^ 4) ∧
  (∀ a e,
    co a e ∈ cs (par a e) ((pTag 0) (co a e))) ∧
  (∀ a Q i,
    ((fs a Q i).card : ℝ) ≤ H ^ 4 * N k ^ (d * ![u, v] a)) ∧
  (∀ a e, fi a e ∈ fs a (par a e) (co a e)) ∧
  (∀ a Q i j, j ∈ fs a Q i → |ofs a Q i j| ≤ H * N k ^ (-r)) ∧
  (∀ a Q i j, j ∈ fs a Q i → ∀ z ∈ fib k r m H Q ((pTag 0) i),
    |MvPolynomial.eval ![z 0, z 2] ((pG a.succ) j) -
      MvPolynomial.eval ![z 0, z 2] ((pG 0) i) - ofs a Q i j| ≤
        H * N k ^ (-r - ![u, v] a)) ∧
  (∀ a Q i x δ, N k ^ (-r - ![u, v] a) ≤ δ →
    (((fs a Q i).filter (fun j => |ofs a Q i j - x| ≤ δ)).card : ℝ) ≤
      H ^ 10 * (δ / N k ^ (-r - ![u, v] a)) ^ d) ∧
  (∀ a tag D j,
    ((Finset.univ.filter (fun Q : Fin (n k r) => ∃ e,
      par a e = Q ∧ (pTag 0) (co a e) = tag ∧ dom a e = D ∧ fi a e = j)).card : ℝ) ≤ H ^ 4))) (fun (k : ℕ) (s m H beta : ℝ) (nn : ℕ) (sets : Fin nn → Set α) (tag : Fin nn → Fin 2 → ℤ) (center velocity : Fin nn → ℝ) (poly : Fin nn → MvPolynomial (Fin 2) ℝ) => 0 < beta ∧ N k ^ (-ℓ * s) / H ≤ beta ∧ beta ≤ H * N k ^ (-ℓ * s) ∧
  (∀ i, MeasurableSet (sets i)) ∧
  (∀ i i', i ≠ i' → Disjoint (sets i) (sets i')) ∧
  (∀ i, |center i| + |velocity i| ≤ H ∧ (poly i).totalDegree ≤ 2 ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, center i + t * velocity i + beta * w] (poly i)| ≤ H) ∧
    (∀ l ∈ sets i,
      ⌊b k l 3 / (N k ^ (-m))⌋ = tag i 0 ∧
      ⌊b k l 0 / (N k ^ (-m))⌋ = tag i 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |(x k l t) 2 - center i - t * velocity i| ≤ H * beta ∧
        |MvPolynomial.eval (x k l t) (P k) -
          MvPolynomial.eval ![t, (x k l t) 2] (poly i)| ≤ H * N k ^ (-s)) ∧
    ENNReal.ofReal (N k ^ (-m) * (N k ^ (-s)) ^ d * beta / H) *
      π k {w : ℝ | ⌊w / (N k ^ (-m))⌋ = tag i 0} ≤
      ρ k (sets i ×ˢ Set.Icc (0 : ℝ) 1)) ∧
  (∑ i, (ENNReal.ofReal (N k ^ (-m) * (N k ^ (-s)) ^ d * beta) * π k {w : ℝ | ⌊w / (N k ^ (-m))⌋ = tag i 0})) ≤ ENNReal.ofReal H)) (fun r u v m => lex r v m ∧ 0 < u ∧ u < r ∧ v < (1 - d) * u / 4 ∧
    10000 * (1 + ℓ) * r < m ∧ (10 / (1 - d) + 4 + ℓ) * u < κ * r)) (fun k r m H Q tag => {z | z 0 ∈ block (T k r) (j k r Q) ∧
    |z 1 - ((tag 1 : ℝ) * N k ^ (-m) + z 0 * ((tag 0 : ℝ) * N k ^ (-m)))| ≤
      H * N k ^ (-m) ∧
    |z 2 - c k r Q 2 - z 0 * c k r Q 3 - c k r Q 4 * z 1| ≤
      H * ((2 : ℝ) ^ (-(T k r : ℤ)) * N k ^ (-ℓ * r))})) (fun k h g width ω => mcode h g width (b k ω.1 1) (b k ω.1 4) ω.2)) (fun h g b a w t => (fun (j : ℤ) => (j, ⌊w / g⌋, ⌊(a + (j : ℝ) * h * w) / b⌋)) ⌊t / h⌋)) (fun k => {ω | ω.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    |b k ω.1 0| + |b k ω.1 1| + |b k ω.1 3| + |b k ω.1 4| ≤ K k})) (∃ L : ℝ, 2 < L ∧ ∀ a : ℝ, 0 < a → L * a < U →
    ∀ D : Finset ℝ, (∀ s ∈ D, a ≤ s ∧ s ≤ 2 * a) → ∀ m : ℝ, L * a < m →
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ H : ℕ → ℝ,
      (∀ k, 1 ≤ H k ∧ K (τ k) ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ N (τ k) ^ ε) ∧
    ∃ (ρ' : ℕ → MeasureTheory.Measure (α × ℝ)) (β : ℕ → ℝ → ℝ) (n' : ℕ → ℝ → ℕ)
      (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
      (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
      (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
      (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),
      (∀ k, ρ' k ≤ ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k Set.univ) ∧
      ∀ k s, s ∈ D →
      0 < β k s ∧ N (τ k) ^ (-ℓ * s) / H k ≤ β k s ∧
      β k s ≤ H k * N (τ k) ^ (-ℓ * s) ∧
      (∀ i, MeasurableSet (C k s i)) ∧
      (∀ i i', i ≠ i' → Disjoint (C k s i) (C k s i')) ∧
      (∀ i, |u k s i| + |v k s i| ≤ H k ∧ (G k s i).totalDegree ≤ 2 ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1,
          |MvPolynomial.eval ![t, u k s i + t * v k s i + β k s * w] (G k s i)| ≤ H k) ∧
        (∀ l ∈ C k s i,
          ⌊b (τ k) l 3 / (N (τ k) ^ (-m))⌋ = tag k s i 0 ∧
          ⌊b (τ k) l 0 / (N (τ k) ^ (-m))⌋ = tag k s i 1 ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            |(x (τ k) l t) 2 - u k s i - t * v k s i| ≤ H k * β k s ∧
            |MvPolynomial.eval (x (τ k) l t) (P (τ k)) -
              MvPolynomial.eval ![t, (x (τ k) l t) 2] (G k s i)| ≤ H k * N (τ k) ^ (-s)) ∧
        ENNReal.ofReal (N (τ k) ^ (-m) * (N (τ k) ^ (-s)) ^ d * β k s / H k) *
          π (τ k) {w : ℝ | ⌊w / (N (τ k) ^ (-m))⌋ = tag k s i 0} ≤
          ρ (τ k) (C k s i ×ˢ Set.Icc (0 : ℝ) 1)) ∧
      (∑ i : Fin (n' k s),
        ENNReal.ofReal (N (τ k) ^ (-m) * (N (τ k) ^ (-s)) ^ d * β k s) *
          π (τ k) {w : ℝ | ⌊w / (N (τ k) ^ (-m))⌋ = tag k s i 0}) ≤ ENNReal.ofReal (H k) ∧
      (∀ᵐ ω ∂ρ' k, ∃ i, ω.1 ∈ C k s i))) (fun r v m => 0 < r ∧ 0 < v ∧ v < r ∧ 100 * (r + v) < m ∧ ℓ * r ≤ m ∧ r + 3 * m / κ < U)) ((∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧
  ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧
  0 ≤ d ∧ d < 1 ∧ 0 < κ ∧ κ ≤ 1 ∧ 0 < ℓ ∧ 0 < S ∧
  S ≤ 1 ∧ 0 < U ∧ 0 < e₀ ∧ basic ∧ caps ∧ prepared ∧ nested)) ((∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ U → ∀ i : Fin (n k t), ∃ h : Fin (n k s), A k t i ⊆ A k s h ∧ block (T k t) (j k t i) ⊆ block (T k s) (j k s h)))) (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ U → atDepth k s R)) (fun k s R => (fun (q : ℝ) => (fun (a : ℝ) => (fun (g : ℝ) => N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧
  (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧
  (∀ i, MeasurableSet (A k s i) ∧ MeasurableSet (B k s i) ∧ B k s i ⊆ A k s i) ∧
  (∀ i i', i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧
  (∀ i,
    ENNReal.ofReal (a ^ d * q ^ 2 * g / K k) ≤ ν k (A k s i) ∧
    ν k (A k s i) ≤ ENNReal.ofReal (K k * a ^ d * q ^ 2 * g) ∧
    ENNReal.ofReal (q / K k) * ν k (A k s i) ≤
      μ k (B k s i ×ˢ block (T k s) (j k s i)) ∧
    (∀ e, |c k s i e| ≤ K k) ∧ (F k s i).totalDegree ≤ 2 ∧
    (∀ l ∈ A k s i, ∀ t ∈ block (T k s) (j k s i),
      |(x k l t) 1 - c k s i 0 - t * c k s i 1| ≤ K k * q ∧
      |(x k l t) 2 - c k s i 2 - t * c k s i 3 - c k s i 4 * (x k l t) 1| ≤
        K k * q * g ∧
      |b k l 4 - c k s i 3 - c k s i 4 * b k l 3| ≤ K k * g) ∧
    (∀ l ∈ B k s i, fit k (K k) a (F k s i) l (block (T k s) (j k s i))) ∧
    (∀ᵐ ω ∂μ k, ω.1 ∈ B k s i → ω.2 ∈ block (T k s) (j k s i) →
      (K k)⁻¹ ≤ |MvPolynomial.eval (x k ω.1 ω.2) (MvPolynomial.pderiv (3 : Fin 4) (F k s i))|)) ∧
  (∀ᵐ ω ∂μ k, ∃ i, ω.1 ∈ B k s i ∧ ω.2 ∈ block (T k s) (j k s i)) ∧
  (∀ (i : Fin (n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R →
    μ k {ω | ω.1 ∈ B k s i ∧ ω.2 ∈ block (T k s) (j k s i) ∧
      ⌊b k ω.1 3 / (N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (K k * q) * ν k (A k s i) *
        π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) (N k ^ (-ℓ * s))) (N k ^ (-s))) ((2 : ℝ) ^ (-(T k s : ℤ))))) ((∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})))) ((∀ k, Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k, |b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k))|)))) (fun k H a Q l I => ∀ t ∈ I, |MvPolynomial.eval (x k l t) Q| ≤ H * a ∧
    |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧
    |MvPolynomial.eval (x k l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a)) (fun k Nk r q e => ⌊(![q.2,(x k q.1 q.2) 1,(x k q.1 q.2) 2] : Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))) (fun k l t => ![t,b k l 0 + t * b k l 3,b k l 1 + t * b k l 4,b k l 2 + t * b k l 5])

def RawListsStatement : Prop :=
(∀ S : ℝ, 0 < S → ∃ C₀ : ℝ, 100 < C₀ ∧ ∀ A θ : ℝ, 0 < A → 0 < θ → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (π : MeasureTheory.Measure ℝ) (b v : α → ℝ) (v₀ χb χv : ℝ) (f : α × ℝ → Fin 2 → ℝ) (L : (ℤ × ℤ) → Finset (Fin 3 → ℝ)), (fun (δ e : ℝ) => (fun (z : α × ℝ → Fin 2 → ℝ) => (fun (state : α × ℝ → Fin 4 → ℤ) => Measurable b → Measurable v → Measurable f → MeasureTheory.IsProbabilityMeasure ν → MeasureTheory.IsProbabilityMeasure π → N ^ (-A) ≤ χb → χb ≤ 1 → N ^ (-A) ≤ χv → χv ≤ 1 → (∀ l, |b l| + |v l| + |v₀| ≤ N ^ η) → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ᵐ p ∂μ, ∀ i, |f p i| ≤ N ^ η) → (∀ q : Fin 2 → ℤ, μ {p | (fun i => ⌊z p i / δ⌋) = q} ≤ ENNReal.ofReal (N ^ η * δ ^ 2)) → (∀ x r : ℝ, δ ≤ r → r ≤ 1 → π (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) → (∀ (q : Fin 4 → ℤ) (j : ℤ), μ {p | state p = q ∧ ⌊v p.1 / δ⌋ = j} ≤ ENNReal.ofReal (N ^ η) * μ {p | state p = q} * π (Set.Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ))) → (∀ q, ((L q).card : ℝ) ≤ N ^ η) → (∀ q, ∀ a ∈ L q, ∀ i, |a i| ≤ N ^ η) → (∀ᵐ p ∂μ, ∃ a ∈ L (⌊b p.1 / χb⌋, ⌊v p.1 / χv⌋), |f p 0 - a 0 - a 1 * p.2| ≤ N ^ η * e ∧ |f p 1 - a 2| ≤ N ^ η * e) → ∃ C : Fin 4 → ℝ, (∀ i, |C i| ≤ N ^ ε) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | |f p 0 - C 0 - C 1 * z p 0 - C 2 * z p 1| ≤ N ^ ε * e ∧ |f p 1 - C 3| ≤ N ^ ε * e}) (fun p => ![⌊z p 0 / δ⌋, ⌊z p 1 / δ⌋, ⌊f p 0 / e⌋, ⌊f p 1 / e⌋])) (fun p => ![p.2, b p.1 + p.2 * (v p.1 - v₀)])) (N ^ (-(C₀ * (A + θ)))) (N ^ (-θ))) → (∀ (α : Type) [MeasurableSpace α] (N K : ℕ → ℝ) (d κ ℓ S U e₀ : ℝ)
  (ν : ℕ → MeasureTheory.Measure α) (μ ρ : ℕ → MeasureTheory.Measure (α × ℝ))
  (π : ℕ → MeasureTheory.Measure ℝ) (b : ℕ → α → Fin 6 → ℝ)
  (P : ℕ → MvPolynomial (Fin 4) ℝ) (T n : ℕ → ℝ → ℕ)
  (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
  (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α)
  (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ)
  (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ),
(fun (x : ℕ → α → ℝ → Fin 4 → ℝ) =>
(fun (block : (T : ℕ) → Fin (2 ^ T) → Set ℝ) =>
(fun (z : ℕ → ℝ → ℝ → (α × ℝ) → Fin 3 → ℤ) =>
(fun (fit : ℕ → ℝ → ℝ → MvPolynomial (Fin 4) ℝ → α → Set ℝ → Prop) =>
(fun (signal : ℕ → α → ℝ → ℝ) =>
(fun (base : ℕ → α → ℝ → Fin 3 → ℝ) =>
(fun (scalarY : (Fin 5 → ℝ) → ℝ → ℝ) =>
(fun (scalarX : (Fin 5 → ℝ) → ℝ → ℝ) =>
(fun (scl : (Fin 5 → ℝ) → ℝ → ℝ → Fin 2 → ℤ) =>
(fun (basic : Prop) =>
(fun (caps : Prop) =>
(fun (atDepth : ℕ → ℝ → ℝ → Prop) =>
(fun (prepared : Prop) =>
(fun (nested : Prop) =>
(fun (valid : Prop) =>
(fun (lex : ℝ → ℝ → ℝ → Prop) =>
(fun (fc : ∀ (k : ℕ) (r v m ε : ℝ) (par : Fin (n k r)) (t₀ q z₀ zv : ℝ)
    (W0 : MvPolynomial (Fin 3) ℝ) (nu0 : MeasureTheory.Measure α)
    (lam : MeasureTheory.Measure (α × ℝ)) (coeff : α → Fin 5 → ℝ)
    (E0 : Set α) (lists : ℤ → Finset ((Fin 2 → ℤ) × ℤ)), Prop) =>
(fun (frames : ℕ → ℝ → ℝ → ℝ → ℝ → Prop) =>
(fun (bgood : ℕ → Set (α × ℝ)) =>
(fun (mcode : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℤ × ℤ × ℤ) =>
(fun (dcode : ℕ → ℝ → ℝ → ℝ → (α × ℝ) → ℤ × ℤ × ℤ) =>
(fun (fib : (k : ℕ) → (r m H : ℝ) → Fin (n k r) → (Fin 2 → ℤ) → Set (Fin 3 → ℝ)) =>
(fun (ce : ℝ → ℝ → ℝ → ℝ → Prop) =>
(fun (layerValid : ∀ (k : ℕ) (s m H beta : ℝ) (nn : ℕ) (sets : Fin nn → Set α) (tag : Fin nn → Fin 2 → ℤ) (center velocity : Fin nn → ℝ) (poly : Fin nn → MvPolynomial (Fin 2) ℝ), Prop) =>
(fun (cc : ∀ (k : ℕ) (r u v m H : ℝ) (beta : Fin 3 → ℝ)
    (pn : Fin 3 → ℕ)
    (pC : (a : Fin 3) → Fin (pn a) → Set α)
    (pTag : (a : Fin 3) → Fin (pn a) → Fin 2 → ℤ)
    (pU : (a : Fin 3) → Fin (pn a) → ℝ)
    (pV : (a : Fin 3) → Fin (pn a) → ℝ)
    (pG : (a : Fin 3) → Fin (pn a) → MvPolynomial (Fin 2) ℝ)
    (lam : MeasureTheory.Measure (α × ℝ))
    (cnt : Fin 2 → ℕ)
    (par : ∀ a, Fin (cnt a) → Fin (n k r))
    (co : ∀ a, Fin (cnt a) → Fin (pn 0))
    (fi : ∀ a, Fin (cnt a) → Fin (pn a.succ))
    (dom : ∀ a, Fin (cnt a) → ℤ × ℤ × ℤ)
    (ev : ∀ a, Fin (cnt a) → Set (α × ℝ))
    (cs : Fin (n k r) → (Fin 2 → ℤ) → Finset (Fin (pn 0)))
    (fs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) →
    Finset (Fin (pn a.succ)))
    (ofs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) → Fin (pn a.succ) → ℝ), Prop) =>
(fun (samples : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) =>
valid → ∃ Λ : ℝ, 0 < Λ ∧ ∀ r u v m : ℝ, ce r u v m → Λ * m ≤ U → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in Filter.atTop, ∀ H : ℝ, 2 ≤ H → K k ≤ H → H ≤ N k ^ δ → samples k r u v m H → frames k r v m ε) (fun k r u v m H => ∃ (beta : Fin 3 → ℝ)
    (pn : Fin 3 → ℕ)
    (pC : (a : Fin 3) → Fin (pn a) → Set α)
    (pTag : (a : Fin 3) → Fin (pn a) → Fin 2 → ℤ)
    (pU : (a : Fin 3) → Fin (pn a) → ℝ)
    (pV : (a : Fin 3) → Fin (pn a) → ℝ)
    (pG : (a : Fin 3) → Fin (pn a) → MvPolynomial (Fin 2) ℝ)
    (lam : MeasureTheory.Measure (α × ℝ))
    (cnt : Fin 2 → ℕ)
    (par : ∀ a, Fin (cnt a) → Fin (n k r))
    (co : ∀ a, Fin (cnt a) → Fin (pn 0))
    (fi : ∀ a, Fin (cnt a) → Fin (pn a.succ))
    (dom : ∀ a, Fin (cnt a) → ℤ × ℤ × ℤ)
    (ev : ∀ a, Fin (cnt a) → Set (α × ℝ))
    (cs : Fin (n k r) → (Fin 2 → ℤ) → Finset (Fin (pn 0)))
    (fs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) →
    Finset (Fin (pn a.succ)))
    (ofs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) → Fin (pn a.succ) → ℝ), cc k r u v m H beta pn pC pTag pU pV pG lam cnt par co fi dom ev cs fs ofs)) (fun (k : ℕ) (r u v m H : ℝ) (beta : Fin 3 → ℝ)
    (pn : Fin 3 → ℕ)
    (pC : (a : Fin 3) → Fin (pn a) → Set α)
    (pTag : (a : Fin 3) → Fin (pn a) → Fin 2 → ℤ)
    (pU : (a : Fin 3) → Fin (pn a) → ℝ)
    (pV : (a : Fin 3) → Fin (pn a) → ℝ)
    (pG : (a : Fin 3) → Fin (pn a) → MvPolynomial (Fin 2) ℝ)
    (lam : MeasureTheory.Measure (α × ℝ))
    (cnt : Fin 2 → ℕ)
    (par : ∀ a, Fin (cnt a) → Fin (n k r))
    (co : ∀ a, Fin (cnt a) → Fin (pn 0))
    (fi : ∀ a, Fin (cnt a) → Fin (pn a.succ))
    (dom : ∀ a, Fin (cnt a) → ℤ × ℤ × ℤ)
    (ev : ∀ a, Fin (cnt a) → Set (α × ℝ))
    (cs : Fin (n k r) → (Fin 2 → ℤ) → Finset (Fin (pn 0)))
    (fs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) →
    Finset (Fin (pn a.succ)))
    (ofs : ∀ a : Fin 2, Fin (n k r) → Fin (pn 0) → Fin (pn a.succ) → ℝ) => (2 ≤ H) ∧
  (∀ a, layerValid k (![r, r + u, r + v] a) m H (beta a) (pn a) (pC a) (pTag a) (pU a) (pV a) (pG a)) ∧
  (∀ a i e, |((pG a) i).coeff e| ≤ N k ^ (m / 1000)) ∧
  (lam ≤ ρ k) ∧
  (ENNReal.ofReal H⁻¹ ≤ lam Set.univ) ∧
  (∀ a e, MeasurableSet (ev a e)) ∧
  (∀ a, Pairwise (fun e f => Disjoint (ev a e) (ev a f))) ∧
  (∀ a, ∀ᵐ ω ∂lam, ∃ e, ω ∈ ev a e) ∧
  (∀ a, Function.Injective
    (fun e => (par a e, co a e, fi a e, dom a e))) ∧
  (∀ a e ω, ω ∈ ev a e →
    ω ∈ bgood k ∧ ω.1 ∈ B k r (par a e) ∧
      ω.2 ∈ block (T k r) (j k r (par a e)) ∧
      ω.1 ∈ (pC 0) (co a e) ∧ ω.1 ∈ (pC a.succ) (fi a e) ∧
      dcode k ((2 : ℝ) ^ (-(T k r : ℤ))) (N k ^ (-ℓ * r))
        ((2 : ℝ) ^ (-(T k r : ℤ)) * N k ^ (-ℓ * r)) ω = dom a e) ∧
  (∀ a e,
    0 < π k {w : ℝ | ⌊w / N k ^ (-m)⌋ = (pTag 0) (co a e) 0}) ∧
  (∀ a e,
    ENNReal.ofReal (((2 : ℝ) ^ (-(T k r : ℤ))) * N k ^ (-m) *
      (((2 : ℝ) ^ (-(T k r : ℤ))) * N k ^ (-ℓ * r)) *
      (N k ^ (-r - ![u, v] a)) ^ d / H) *
      π k {w : ℝ | ⌊w / N k ^ (-m)⌋ = (pTag 0) (co a e) 0} ≤ lam (ev a e)) ∧
  (∀ a,
    (∑ e, ENNReal.ofReal (((2 : ℝ) ^ (-(T k r : ℤ))) * N k ^ (-m) *
      (((2 : ℝ) ^ (-(T k r : ℤ))) * N k ^ (-ℓ * r)) *
      (N k ^ (-r - ![u, v] a)) ^ d) *
      π k {w : ℝ | ⌊w / N k ^ (-m)⌋ = (pTag 0) (co a e) 0}) ≤ ENNReal.ofReal H) ∧
  (∀ Q tag, ((cs Q tag).card : ℝ) ≤ H ^ 4) ∧
  (∀ a e,
    co a e ∈ cs (par a e) ((pTag 0) (co a e))) ∧
  (∀ a Q i,
    ((fs a Q i).card : ℝ) ≤ H ^ 4 * N k ^ (d * ![u, v] a)) ∧
  (∀ a e, fi a e ∈ fs a (par a e) (co a e)) ∧
  (∀ a Q i j, j ∈ fs a Q i → |ofs a Q i j| ≤ H * N k ^ (-r)) ∧
  (∀ a Q i j, j ∈ fs a Q i → ∀ z ∈ fib k r m H Q ((pTag 0) i),
    |MvPolynomial.eval ![z 0, z 2] ((pG a.succ) j) -
      MvPolynomial.eval ![z 0, z 2] ((pG 0) i) - ofs a Q i j| ≤
        H * N k ^ (-r - ![u, v] a)) ∧
  (∀ a Q i x δ, N k ^ (-r - ![u, v] a) ≤ δ →
    (((fs a Q i).filter (fun j => |ofs a Q i j - x| ≤ δ)).card : ℝ) ≤
      H ^ 10 * (δ / N k ^ (-r - ![u, v] a)) ^ d) ∧
  (∀ a tag D j,
    ((Finset.univ.filter (fun Q : Fin (n k r) => ∃ e,
      par a e = Q ∧ (pTag 0) (co a e) = tag ∧ dom a e = D ∧ fi a e = j)).card : ℝ) ≤ H ^ 4))) (fun (k : ℕ) (s m H beta : ℝ) (nn : ℕ) (sets : Fin nn → Set α) (tag : Fin nn → Fin 2 → ℤ) (center velocity : Fin nn → ℝ) (poly : Fin nn → MvPolynomial (Fin 2) ℝ) => 0 < beta ∧ N k ^ (-ℓ * s) / H ≤ beta ∧ beta ≤ H * N k ^ (-ℓ * s) ∧
  (∀ i, MeasurableSet (sets i)) ∧
  (∀ i i', i ≠ i' → Disjoint (sets i) (sets i')) ∧
  (∀ i, |center i| + |velocity i| ≤ H ∧ (poly i).totalDegree ≤ 2 ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, center i + t * velocity i + beta * w] (poly i)| ≤ H) ∧
    (∀ l ∈ sets i,
      ⌊b k l 3 / (N k ^ (-m))⌋ = tag i 0 ∧
      ⌊b k l 0 / (N k ^ (-m))⌋ = tag i 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |(x k l t) 2 - center i - t * velocity i| ≤ H * beta ∧
        |MvPolynomial.eval (x k l t) (P k) -
          MvPolynomial.eval ![t, (x k l t) 2] (poly i)| ≤ H * N k ^ (-s)) ∧
    ENNReal.ofReal (N k ^ (-m) * (N k ^ (-s)) ^ d * beta / H) *
      π k {w : ℝ | ⌊w / (N k ^ (-m))⌋ = tag i 0} ≤
      ρ k (sets i ×ˢ Set.Icc (0 : ℝ) 1)) ∧
  (∑ i, (ENNReal.ofReal (N k ^ (-m) * (N k ^ (-s)) ^ d * beta) * π k {w : ℝ | ⌊w / (N k ^ (-m))⌋ = tag i 0})) ≤ ENNReal.ofReal H)) (fun r u v m => lex r v m ∧ 0 < u ∧ u < r ∧ v < (1 - d) * u / 4 ∧
    10000 * (1 + ℓ) * r < m ∧ (10 / (1 - d) + 4 + ℓ) * u < κ * r)) (fun k r m H Q tag => {z | z 0 ∈ block (T k r) (j k r Q) ∧
    |z 1 - ((tag 1 : ℝ) * N k ^ (-m) + z 0 * ((tag 0 : ℝ) * N k ^ (-m)))| ≤
      H * N k ^ (-m) ∧
    |z 2 - c k r Q 2 - z 0 * c k r Q 3 - c k r Q 4 * z 1| ≤
      H * ((2 : ℝ) ^ (-(T k r : ℤ)) * N k ^ (-ℓ * r))})) (fun k h g width ω => mcode h g width (b k ω.1 1) (b k ω.1 4) ω.2)) (fun h g b a w t => (fun (j : ℤ) => (j, ⌊w / g⌋, ⌊(a + (j : ℝ) * h * w) / b⌋)) ⌊t / h⌋)) (fun k => {ω | ω.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    |b k ω.1 0| + |b k ω.1 1| + |b k ω.1 3| + |b k ω.1 4| ≤ K k})) (fun k r v m ε => ∃ (par : Fin (n k r)) (t₀ q z₀ zv : ℝ)
    (W0 : MvPolynomial (Fin 3) ℝ) (nu0 : MeasureTheory.Measure α)
    (lam : MeasureTheory.Measure (α × ℝ)) (coeff : α → Fin 5 → ℝ)
    (E0 : Set α) (lists : ℤ → Finset ((Fin 2 → ℤ) × ℤ)), fc k r v m ε par t₀ q z₀ zv W0 nu0 lam coeff E0 lists)) (fun (k : ℕ) (r v m ε : ℝ) (par : Fin (n k r)) (t₀ q z₀ zv : ℝ)
    (W0 : MvPolynomial (Fin 3) ℝ) (nu0 : MeasureTheory.Measure α)
    (lam : MeasureTheory.Measure (α × ℝ)) (coeff : α → Fin 5 → ℝ)
    (E0 : Set α) (lists : ℤ → Finset ((Fin 2 → ℤ) × ℤ)) => (MeasurableSet E0) ∧
  (E0 ⊆ B k r par) ∧
  (Measurable coeff) ∧
  (MeasureTheory.IsProbabilityMeasure nu0) ∧
  (lam ≤ ENNReal.ofReal (N k ^ ε) • (nu0.prod MeasureTheory.volume)) ∧
  (lam (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧
  (∀ᵐ ω ∂lam, ω.1 ∈ E0) ∧
  (∀ l i, |coeff l i| ≤ N k ^ ε) ∧
  (ENNReal.ofReal (N k ^ (-ε)) ≤ lam Set.univ) ∧
  (0 < q) ∧
  (q = ((2 : ℝ) ^ T k r)⁻¹) ∧
  (block (T k r) (j k r par) = Set.Icc t₀ (t₀ + q)) ∧
  (W0.totalDegree ≤ 2) ∧
  ((∑ e ∈ W0.support, |W0.coeff e|) ≤ N k ^ (m / 10)) ∧
  (1 + |q⁻¹| * (2 + |t₀| + |z₀| + |zv|) ≤ N k ^ (m / 10)) ∧
  (∀ l ∈ E0, ∀ u,
    scalarY (coeff l) u = (x k l (t₀ + q * u) 1 - z₀ - zv * (t₀ + q * u)) / q) ∧
  (∀ l ∈ E0, ∀ u,
    scalarX (coeff l) u = signal k l (t₀ + q * u) -
      MvPolynomial.eval (base k l (t₀ + q * u)) W0) ∧
  ((ENNReal.ofReal q * ν k (A k r par)) •
      lam.map (fun ω => (ω.1, t₀ + q * ω.2)) ≤ ρ k) ∧
  (∀ a : ℤ, ((lists a).card : ℝ) * (N k ^ (-m)) ^ 2 ≤
    N k ^ ε * N k ^ (d * v)) ∧
  (∀ᵐ ω ∂lam,
    (scl (coeff ω.1) ω.2 (N k ^ (-m)),
      ⌊scalarX (coeff ω.1) ω.2 / N k ^ (-r - v)⌋) ∈
      lists ⌊b k ω.1 3 / N k ^ (-m)⌋))) (fun r v m => 0 < r ∧ 0 < v ∧ v < r ∧ 100 * (r + v) < m ∧ ℓ * r ≤ m ∧ r + 3 * m / κ < U)) ((∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧
  ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧
  0 ≤ d ∧ d < 1 ∧ 0 < κ ∧ κ ≤ 1 ∧ 0 < ℓ ∧ 0 < S ∧
  S ≤ 1 ∧ 0 < U ∧ 0 < e₀ ∧ basic ∧ caps ∧ prepared ∧ nested)) ((∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s t : ℝ, R⁻¹ ≤ s → s < t → t ≤ U → ∀ i : Fin (n k t), ∃ h : Fin (n k s), A k t i ⊆ A k s h ∧ block (T k t) (j k t i) ⊆ block (T k s) (j k s h)))) (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ U → atDepth k s R)) (fun k s R => (fun (q : ℝ) => (fun (a : ℝ) => (fun (g : ℝ) => N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧
  (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧
  (∀ i, MeasurableSet (A k s i) ∧ MeasurableSet (B k s i) ∧ B k s i ⊆ A k s i) ∧
  (∀ i i', i ≠ i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧
  (∀ i,
    ENNReal.ofReal (a ^ d * q ^ 2 * g / K k) ≤ ν k (A k s i) ∧
    ν k (A k s i) ≤ ENNReal.ofReal (K k * a ^ d * q ^ 2 * g) ∧
    ENNReal.ofReal (q / K k) * ν k (A k s i) ≤
      μ k (B k s i ×ˢ block (T k s) (j k s i)) ∧
    (∀ e, |c k s i e| ≤ K k) ∧ (F k s i).totalDegree ≤ 2 ∧
    (∀ l ∈ A k s i, ∀ t ∈ block (T k s) (j k s i),
      |(x k l t) 1 - c k s i 0 - t * c k s i 1| ≤ K k * q ∧
      |(x k l t) 2 - c k s i 2 - t * c k s i 3 - c k s i 4 * (x k l t) 1| ≤
        K k * q * g ∧
      |b k l 4 - c k s i 3 - c k s i 4 * b k l 3| ≤ K k * g) ∧
    (∀ l ∈ B k s i, fit k (K k) a (F k s i) l (block (T k s) (j k s i))) ∧
    (∀ᵐ ω ∂μ k, ω.1 ∈ B k s i → ω.2 ∈ block (T k s) (j k s i) →
      (K k)⁻¹ ≤ |MvPolynomial.eval (x k ω.1 ω.2) (MvPolynomial.pderiv (3 : Fin 4) (F k s i))|)) ∧
  (∀ᵐ ω ∂μ k, ∃ i, ω.1 ∈ B k s i ∧ ω.2 ∈ block (T k s) (j k s i)) ∧
  (∀ (i : Fin (n k s)) (v : ℝ) (v₀ : ℤ), R⁻¹ ≤ v → v ≤ R →
    μ k {ω | ω.1 ∈ B k s i ∧ ω.2 ∈ block (T k s) (j k s i) ∧
      ⌊b k ω.1 3 / (N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (K k * q) * ν k (A k s i) *
        π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})) (N k ^ (-ℓ * s))) (N k ^ (-s))) ((2 : ℝ) ^ (-(T k s : ℤ))))) ((∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R → (∀ a : ℤ, π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-S * v))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s))) ∧ (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ), μ k {p | z k (N k) r p = q ∧ ⌊(if h then MvPolynomial.eval (x k p.1 p.2) (P k) else (x k p.1 p.2) 3) / (N k ^ (-s))⌋ = a ∧ ⌊b k p.1 3 / (N k ^ (-v))⌋ = v₀} ≤ ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * π k {w : ℝ | ⌊w / (N k ^ (-v))⌋ = v₀})))) ((∀ k, Measurable (b k) ∧ MeasureTheory.IsProbabilityMeasure (ν k) ∧ MeasureTheory.IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod MeasureTheory.volume) ∧ ρ k ≤ μ k ∧ μ k (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ρ k Set.univ ∧ (P k).totalDegree ≤ 2 ∧ (∀ᵐ l ∂ν k, |b k l 0| + |b k l 1| + |b k l 3| + |b k l 4| ≤ K k) ∧ (∀ᵐ p ∂μ k, (∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (x k p.1 t) (P k)| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (P k))| ≤ K k ∧ |MvPolynomial.eval (x k p.1 t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k)))| ≤ K k) ∧ (K k)⁻¹ ≤ |MvPolynomial.eval (x k p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k))|)))) (fun a t σ => ![⌊t / σ⌋,⌊scalarY a t / σ⌋])) (fun a t => a 2 + t * a 3 + t ^ 2 * a 4)) (fun a t => a 0 + t * a 1)) (fun k l t => x k l t ∘ Fin.castSucc)) (fun k l t => MvPolynomial.eval (x k l t) (P k))) (fun k H a Q l I => ∀ t ∈ I, |MvPolynomial.eval (x k l t) Q| ≤ H * a ∧
    |MvPolynomial.eval (x k l t) (MvPolynomial.pderiv (3 : Fin 4) Q)| ≤ H ∧
    |MvPolynomial.eval (x k l t)
      (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) Q))| ≤ H / a)) (fun k Nk r q e => ⌊(![q.2,(x k q.1 q.2) 1,(x k q.1 q.2) 2] : Fin 3 → ℝ) e / (Nk ^ (-r))⌋)) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))) (fun k l t => ![t,b k l 0 + t * b k l 3,b k l 1 + t * b k l 4,b k l 2 + t * b k l 5]))

end Submission.Obl.k4_general_parent_wide_layer_candidates.Split
