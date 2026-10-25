/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/Interface.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/Interface.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Mathlib
import ChallengeDeps

/-! Named forms of the immediately applied lambda definitions in the frozen
statement. These definitions retain the original trajectory law, all chart
floors, and the fixed-format quantifier order. -/

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

def x : (ℕ × (Fin 6 → ℝ)) → ℝ → Fin 4 → ℝ :=
  (fun l t => ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5])

def y : (ℕ × (Fin 6 → ℝ)) → ℝ → EuclideanSpace ℝ (Fin 2) :=
  (fun l t => WithLp.toLp 2 ![(x l t) 1, (x l t) 2])

def v : (ℕ × (Fin 6 → ℝ)) → EuclideanSpace ℝ (Fin 2) :=
  (fun l => WithLp.toLp 2 ![l.2 3, l.2 4])

def δ : ℝ → ℝ → ℝ :=
  (fun N r => (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ)))

def obs : ℝ → ℝ → ((ℕ × (Fin 6 → ℝ)) × ℝ) → (EuclideanSpace ℝ (Fin 3) × ℤ) :=
  (fun B a p => (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2], ⌊B * (x p.1 p.2) 3 / a⌋))

def fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop :=
  (fun n H D A => ∃ m₀ : ℕ, (m₀ : ℝ) ≤ H ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin n) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ A ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)

def prob : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → ℝ → ℝ → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ((k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal) → ((k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal) → Prop :=
  (fun N K L d S η W ω ν E P B f g G => (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧ 0 < L ∧ 0 < d ∧ d < 1 ∧ 0 < S ∧ 0 < η ∧ (fun μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) => (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (fmt 6 (N k ^ M) D (A j)) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (fmt 7 (N k ^ M) D ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}))) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k ∧ |MvPolynomial.eval (x l t) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(μ k γ), B k γ / K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) Set.univ) ∧ (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map (obs (B k γ) (δ (N k) r)) (μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) ∧ (∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧ MeasureTheory.Measure.map (fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) (μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) ∧ (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) ∧ (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | g k γ r ((obs (B k γ) (δ (N k) r)) p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((obs (B k γ) (δ (N k) r)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) ∧ (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) ∧ (∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c)))) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ)))

def chart : ℝ → ℕ → ℕ → ℝ → ℕ → ℝ → ℝ → ℝ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ → MvPolynomial (Fin 4) ℝ → Set (ℕ × (Fin 6 → ℝ)) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop → Prop :=
  (fun Nk M D κ T j r Bv Ev c u Q R A F ex => Matrix.det Q ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧ R.totalDegree ≤ 2 ∧ (∀ e, |R.coeff e| ≤ Nk ^ M) ∧ MeasurableSet A ∧ MeasurableSet F ∧ (∀ i, fmt 6 (Nk ^ M) D {x | (i, x) ∈ A} ∧ fmt 7 (Nk ^ M) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) ∧ (∀ l ∈ A, (l.1 : ℝ) ≤ Nk ^ M ∧ (∀ e, |l.2 e| ≤ Nk ^ M) ∧ ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ ∧ |MvPolynomial.eval (x l t) R| ≤ κ * δ Nk r ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * Bv ∧ |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ κ * Bv ^ 2 / δ Nk r) ∧ (∀ p ∈ F, p ∈ Ev ∧ p.1 ∈ A ∧ p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧ Bv / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) ∧ ex)

def term : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ → Prop :=
  (fun N K L W ω ν E B f h => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ N k ^ h ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * (((ν k (γ b)).prod MeasureTheory.volume) (F b)))

def H : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ :=
  (fun N K L W ω ν E B f => sInf {h : ℝ | term N K L W ω ν E B f h})

def nt : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop :=
  (fun N K L W ω ν E B f h w => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (∀ b, |Matrix.det (Q b)| * (4 : ℝ) ^ T ≤ N k ^ (-w + ε)) ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * (((ν k (γ b)).prod MeasureTheory.volume) (F b)))

def es : ℝ → ℝ → ℝ → ℝ → Prop :=
  (fun ds kr S η => 0 ≤ ds ∧ ds < 1 ∧ 0 < kr ∧ kr ≤ 1 ∧ (∀ t : ℝ, 0 < t → ∃ N K d W ω ν E P B f g G, prob N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧ kr - t < H N K 1 W ω ν E B f) ∧ (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧ ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G → d < ds + a → H N K L W ω ν E B f ≤ (kr + t) * L) ∧ (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧ ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G → d < ds + a → (kr - a) * L < H N K L W ω ν E B f → ∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - ds * r| ≤ t * L))

def bw : ℝ → ℝ → ℝ → ℝ → Prop :=
  (fun ds kr S η => ∃ a w : ℝ, 0 < a ∧ 0 ≤ w ∧ ∀ t : ℝ, 0 < t → ∃ N K d W ω ν E P B f g G, prob N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧ kr - t < H N K 1 W ω ν E B f ∧ ¬ nt N K 1 W ω ν E B f (kr + a) w)

def ScalarMeshProjection : Prop :=
  (∀ d s m C S U ε : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (c : ℝ) (angular : Bool), (fun a : ℝ => (fun σ : ℝ => (fun y : α → ℝ → ℝ => (fun x : α → ℝ → ℝ => (fun z : α × ℝ → Fin 2 → ℤ => Measurable b → MeasureTheory.IsProbabilityMeasure ν → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ l i, |b l i| ≤ N ^ η) → N ^ (-C) ≤ c → c ≤ N ^ C → (∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s → μ {p | z p = q ∧ ⌊x p.1 p.2 / (N ^ (-r))⌋ = j} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * (N ^ (-r)) ^ d)) → (∃ F : Finset ((Fin 2 → ℤ) × ℤ), (F.card : ℝ) * σ ^ 2 ≤ N ^ η * c⁻¹ * a ^ (-d) ∧ ∀ᵐ p ∂μ, (z p, ⌊x p.1 p.2 / a⌋) ∈ F) → (angular = true → ∀ (r : ℝ) (q : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U → μ {p | z p = q ∧ ⌊x p.1 p.2 / a⌋ = j ∧ ⌊b p.1 1 / (N ^ (-r))⌋ = k} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * a ^ d * N ^ (-S * r))) → ∃ (n : ℕ) (β : ℝ) (A : Fin n → Set α) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), σ / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧ (angular = true → N ^ (-ε) ≤ β) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧ (∀ l ∈ A i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * a) ∧ ENNReal.ofReal (c * a ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | ∃ i, p.1 ∈ A i}) (fun p => ![⌊p.2 / σ⌋, ⌊y p.1 p.2 / σ⌋])) (fun l t => b l 2 + t * b l 3 + t ^ 2 * b l 4)) (fun l t => b l 0 + t * b l 1)) (N ^ (-m))) (N ^ (-s)))

def TwoColorMatching : Prop :=
  (∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) → (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) → (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) → (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) → (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) → (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) → ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0)

def InitialHorizonBound : Prop :=
  (∀ N K L d S η W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G → ∀ h : ℝ, L < h → term N K L W ω ν E B f h)

end Submission.Obl.k4_uncapped_native_capping.UWE
