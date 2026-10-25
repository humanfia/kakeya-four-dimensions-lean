import Mathlib
import ChallengeDeps

noncomputable section

namespace Submission.Obl.k4_scalar_mesh_block_reduction

def Subpower (N K : ℕ → ℝ) : Prop :=
(∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε

def Noise (σ : ℝ) : MeasureTheory.Measure (Fin 5 → ℝ) :=
MeasureTheory.Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) σ))

def MarkedPrior (σ : ℝ) (H : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) : MeasureTheory.Measure (ℕ × (Fin 5 → ℝ)) :=
∑ j, ENNReal.ofReal (w j) • MeasureTheory.Measure.map (fun u : Fin 5 → ℝ => ((j : ℕ), b₀ j + u)) (Noise σ)

def MarkedEvent (H J : ℕ) (mark : Fin H → Fin J → Bool) : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
{p | ∃ j : Fin H, p.1.1 = (j : ℕ) ∧ ∃ z : Fin J, mark j z = true ∧ p.2 ∈ Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))}

def MarkedLaw (σ : ℝ) (H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
((MarkedPrior σ H b₀ w).prod MeasureTheory.volume).restrict (MarkedEvent H J mark)

def MeshInput (N K d s m S U : ℝ) (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (c : ℝ) (angular : Bool) : Prop :=
((fun (a : ℝ) =>
((fun (σ : ℝ) =>
((fun (y : α → ℝ → ℝ) =>
((fun (x : α → ℝ → ℝ) =>
((fun (z : α × ℝ → Fin 2 → ℤ) =>
Measurable b ∧ MeasureTheory.IsProbabilityMeasure ν ∧
μ ≤ ENNReal.ofReal K • (ν.prod MeasureTheory.volume) ∧
μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ENNReal.ofReal (K⁻¹) ≤ μ Set.univ ∧
(∀ l i, |b l i| ≤ K) ∧
(∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s →
μ {p | z p = q ∧ ⌊x p.1 p.2 / (N ^ (-r))⌋ = j} ≤ ENNReal.ofReal (K * σ ^ 2 * c * (N ^ (-r)) ^ d)) ∧
(∃ F : Finset ((Fin 2 → ℤ) × ℤ), (F.card : ℝ) * σ ^ 2 ≤ K * c⁻¹ * a ^ (-d) ∧ ∀ᵐ p ∂μ, (z p, ⌊x p.1 p.2 / a⌋) ∈ F) ∧
(angular = true → ∀ (r : ℝ) (q : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U →
μ {p | z p = q ∧ ⌊x p.1 p.2 / a⌋ = j ∧ ⌊b p.1 1 / (N ^ (-r))⌋ = k} ≤ ENNReal.ofReal (K * σ ^ 2 * c * a ^ d * N ^ (-S * r)))) (fun p : α × ℝ => (![⌊p.2 / σ⌋, ⌊y p.1 p.2 / σ⌋] : Fin 2 → ℤ)))) (fun l t => b l 2 + t * b l 3 + t ^ 2 * b l 4))) (fun l t => b l 0 + t * b l 1))) (N ^ (-m)))) (N ^ (-s)))

def Tables (N K m : ℝ) (M H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) : Prop :=
1 ≤ J ∧ (H : ℝ) ≤ N ^ (M : ℝ) ∧ (J : ℝ) ≤ N ^ (M : ℝ) ∧
1 ≤ (J : ℝ) * N ^ (-m) ∧ (J : ℝ) * N ^ (-m) ≤ 2 ∧
(∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ (∀ j e, |b₀ j e| ≤ K) ∧
ENNReal.ofReal (K⁻¹) ≤ MarkedLaw (N ^ (-m)) H J b₀ w mark Set.univ

def Coupling (N K s m : ℝ) (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) : Prop :=
Measurable tag ∧
(∀ j, ENNReal.ofReal (w j) = ν {l | tag l = j}) ∧
(∀ l e, |b l e - b₀ (tag l) e| ≤ N ^ (-10 * (m + s + 1))) ∧
(∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤
μ {p | tag p.1 = j ∧ p.2 ∈ Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))})

def RawEstimates (N K d s m S U c : ℝ) (angular : Bool) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) : Prop :=
((fun (y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) =>
((fun (x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) =>
((fun (obs : ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → ((Fin 2 → ℝ) × ℤ)) =>
((fun (ref : MeasureTheory.Measure ((Fin 2 → ℝ) × ℤ)) =>
(∀ r : ℝ, 0 ≤ r → r ≤ s → ∃ g : ((Fin 2 → ℝ) × ℤ) → ENNReal,
Measurable g ∧ MeasureTheory.Measure.map (obs r) μ = ref.withDensity g ∧
∀ᵐ z ∂ref, g z ≤ ENNReal.ofReal (K * c * N ^ (-d * r))) ∧
(∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) →
∃ G : (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal,
Measurable G ∧ MeasureTheory.Measure.map (fun p => (obs r p, (⌊p.1.2 1 / (N ^ (-u))⌋ : ℤ))) μ = (ref.prod MeasureTheory.Measure.count).withDensity G ∧
(∀ᵐ z ∂(ref.prod MeasureTheory.Measure.count), G z ≤ ENNReal.ofReal (K * c * N ^ (-d * r) * min 1 (N ^ (m - u)))) ∧
(r = s → angular = true → 0 < u → u ≤ U → ∀ᵐ z ∂(ref.prod MeasureTheory.Measure.count), G z ≤ ENNReal.ofReal (K * c * N ^ (-d * s - S * u)))) ∧
(∃ B : Set ((Fin 2 → ℝ) × ℤ), MeasurableSet B ∧ ref B ≤ ENNReal.ofReal (K * c⁻¹ * N ^ (d * s)) ∧ ∀ᵐ p ∂μ, obs s p ∈ B)) (MeasureTheory.volume.prod (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)))) (fun (r : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) => ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N ^ (-r))⌋ : ℤ))))) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4))) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 0 + t * l.2 1))

def BlockOutput (N d s m c ε : ℝ) (angular : Bool) (α : Type) [MeasurableSpace α] (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) : Prop :=
((fun (y : α → ℝ → ℝ) =>
((fun (x : α → ℝ → ℝ) =>
∃ (n : ℕ) (β t₀ q : ℝ) (A : Fin n → Set α) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ),
N ^ (-ε) ≤ q ∧ 0 ≤ t₀ ∧ t₀ + q ≤ 1 ∧ N ^ (-m) / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧
(angular = true → N ^ (-ε) ≤ β) ∧
(∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
(∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧
(∀ t ∈ Set.Icc t₀ (t₀ + q), ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧
(∀ l ∈ A i, ∀ t ∈ Set.Icc t₀ (t₀ + q), |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * N ^ (-s)) ∧
ENNReal.ofReal (c * (N ^ (-s)) ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc (0 : ℝ) 1)) ∧
ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | ∃ i, p.1 ∈ A i}) (fun l t => b l 2 + t * b l 3 + t ^ 2 * b l 4))) (fun l t => b l 0 + t * b l 1))

def NoisyOutput (N d s m c ε : ℝ) (angular : Bool) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) : Prop :=
((fun (y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) =>
((fun (x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) =>
∃ (n : ℕ) (β t₀ q : ℝ) (A : Fin n → Set (ℕ × (Fin 5 → ℝ))) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ),
N ^ (-ε) ≤ q ∧ 0 ≤ t₀ ∧ t₀ + q ≤ 1 ∧ N ^ (-m) / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧
(angular = true → N ^ (-ε) ≤ β) ∧
(∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
(∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧
(∀ t ∈ Set.Icc t₀ (t₀ + q), ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧
(∀ l ∈ A i, ∀ t ∈ Set.Icc t₀ (t₀ + q), |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * N ^ (-s)) ∧
ENNReal.ofReal (q * c * (N ^ (-s)) ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc t₀ (t₀ + q))) ∧
ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | (∃ i, p.1 ∈ A i) ∧ p.2 ∈ Set.Icc t₀ (t₀ + q)}) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4))) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 0 + t * l.2 1))

def ProfileShape (d s m S U C₀ : ℝ) (angular : Bool) (F : ℝ → ℝ → ℝ) : Prop :=
(∀ r r' u : ℝ, 0 ≤ r → r ≤ r' → r' ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) → 0 ≤ F r' u - F r u ∧ F r' u - F r u ≤ r' - r) ∧
(∀ r u u' : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ u' → u' ≤ 4 * (m + s + 1) → 0 ≤ F r u' - F r u ∧ F r u' - F r u ≤ u' - u) ∧
F s 0 = d * s - C₀ ∧
(∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) → d * r - C₀ + max 0 (u - m) ≤ F r u) ∧
(angular = true → ∀ u : ℝ, 0 ≤ u → u ≤ U → F s 0 + S * u ≤ F s u)

def Homogeneous (N : ℕ → ℝ) (s V : ℝ) (μ : ℕ → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (F : ℝ → ℝ → ℝ) : Prop :=
((fun (y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) =>
((fun (x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) =>
((fun (obs : ℕ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → ((Fin 2 → ℝ) × ℤ)) =>
((fun (aug : ℕ → ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → (((Fin 2 → ℝ) × ℤ) × ℤ)) =>
((fun (ref : MeasureTheory.Measure ((Fin 2 → ℝ) × ℤ)) =>
∃ (g : ℕ → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal)
(G : ℕ → ℝ → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal),
(∀ k r, 0 ≤ r → r ≤ s → Measurable (g k r) ∧ MeasureTheory.Measure.map (obs k r) (μ k) = ref.withDensity (g k r)) ∧
(∀ k r u, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V → Measurable (G k r u) ∧ MeasureTheory.Measure.map (aug k r u) (μ k) = (ref.prod MeasureTheory.Measure.count).withDensity (G k r u)) ∧
(∀ r τ : ℝ, 0 ≤ r → r ≤ s → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop,
μ k {p | g k r (obs k r p) < ENNReal.ofReal (N k ^ (-F r 0 - τ)) ∨ ENNReal.ofReal (N k ^ (-F r 0 + τ)) < g k r (obs k r p)} ≤ ENNReal.ofReal (N k ^ (-c))) ∧
(∀ r u τ : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop,
μ k {p | G k r u (aug k r u p) < ENNReal.ofReal (N k ^ (-F r u - τ)) ∨ ENNReal.ofReal (N k ^ (-F r u + τ)) < G k r u (aug k r u p)} ≤ ENNReal.ofReal (N k ^ (-c)))) (MeasureTheory.volume.prod (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)))) (fun (k : ℕ) (r u : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) => (obs k r p, (⌊p.1.2 1 / (N k ^ (-u))⌋ : ℤ))))) (fun (k : ℕ) (r : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) => ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-r))⌋ : ℤ))))) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4))) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 0 + t * l.2 1))

def ExactAngularPackets  : Prop :=
∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ (M D : ℕ) (L d S U : ℝ), 1 ≤ M → 1 ≤ D → 0 < L → 0 ≤ d → d < 1 → 0 < S → 0 < U → ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (g : (k : ℕ) → Fin (W k) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal) (G : (k : ℕ) → Fin (W k) → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal) (f : ℝ → ℝ), (fun (y x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) (μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (fmt : (n : ℕ) → ℝ → ℕ → Set (Fin n → ℝ) → Prop) => (∀ k, (W k : ℝ) ≤ N k ^ (M : ℝ) ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ (∃ n : ℕ, (n : ℝ) ≤ N k ^ (M : ℝ) ∧ ∃ (h : Fin n → ℝ) (i : Fin n → ℕ) (B : Fin n → Set (Fin 5 → ℝ)), (∀ j, 0 ≤ h j ∧ h j ≤ N k ^ (M : ℝ) ∧ (i j : ℝ) ≤ N k ^ (M : ℝ) ∧ fmt 5 (N k ^ (M : ℝ)) D (B j) ∧ (∀ b ∈ B j, ∀ e, |b e| ≤ N k ^ (M : ℝ))) ∧ ν k γ = ∑ j, ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j, b)) (MeasureTheory.volume.restrict (B j))) ∧ (∀ᵐ l ∂ν k γ, ∀ e, |l.2 e| ≤ K k) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ (M : ℝ)) ∧ (∀ i : ℕ, fmt 6 (N k ^ (M : ℝ)) D {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ E k γ})) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * μ k γ Set.univ) → (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧ MeasureTheory.Measure.map (fun p => ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-r))⌋ : ℤ))) (μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) → (∀ k γ u, 0 < u → u ≤ U → Measurable (G k γ u) ∧ MeasureTheory.Measure.map (fun p => (((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-L))⌋ : ℤ)), (⌊p.1.2 1 / (N k ^ (-u))⌋ : ℤ))) (μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) → (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧ f s - f r ≤ s - r) → (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * μ k γ {p | g k γ r ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-r))⌋ : ℤ)) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-r))⌋ : ℤ))}) ≤ ENNReal.ofReal (N k ^ (-c))) → (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) → (∀ u τ : ℝ, 0 < u → u ≤ U → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * μ k γ {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u (((![p.2, y p.1 p.2] : Fin 2 → ℝ), (⌊x p.1 p.2 / (N k ^ (-L))⌋ : ℤ)), (⌊p.1.2 1 / (N k ^ (-u))⌋ : ℤ))}) ≤ ENNReal.ofReal (N k ^ (-c))) → ∀ h ε : ℝ, 0 < h → 0 < ε → ∃ᶠ k in Filter.atTop, ∃ (T n : ℕ) (γ : Fin n → Fin (W k)) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set (ℕ × (Fin 5 → ℝ))) (P : Fin n → MvPolynomial (Fin 2) ℝ), (2 : ℝ) ^ T ≤ N k ^ h ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) ∧ (∀ i, (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, w] (P i)| ≤ N k ^ ε) ∧ (∀ l ∈ A i, ∀ t ∈ Set.Icc (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T), |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N k ^ ε * N k ^ (-L)) ∧ ENNReal.ofReal (N k ^ (-f L) / (N k ^ ε * (2 : ℝ) ^ T)) ≤ μ k (γ i) (A i ×ˢ Set.Icc (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))) ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ ∑ g : Fin (W k), ENNReal.ofReal (ω k g) * μ k g {p | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ Set.Icc (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)}) (fun l t => l.2 0 + t * l.2 1) (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) (fun (n : ℕ) (B : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) => ∃ k : ℕ, (k : ℝ) ≤ B ∧ ∃ p : Fin k → MvPolynomial (Fin n) ℝ, (∀ j, (p j).totalDegree ≤ D ∧ ∀ b, |(p j).coeff b| ≤ B) ∧ ∃ S : Set (Fin k → SignType), A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S})

def MeshBlockPackets  : Prop :=
(∀ d s m C S U ε : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (c : ℝ) (angular : Bool), (fun a : ℝ => (fun σ : ℝ => (fun y : α → ℝ → ℝ => (fun x : α → ℝ → ℝ => (fun z : α × ℝ → Fin 2 → ℤ => Measurable b → MeasureTheory.IsProbabilityMeasure ν → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ l i, |b l i| ≤ N ^ η) → N ^ (-C) ≤ c → c ≤ N ^ C → (∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s → μ {p | z p = q ∧ ⌊x p.1 p.2 / (N ^ (-r))⌋ = j} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * (N ^ (-r)) ^ d)) → (∃ F : Finset ((Fin 2 → ℤ) × ℤ), (F.card : ℝ) * σ ^ 2 ≤ N ^ η * c⁻¹ * a ^ (-d) ∧ ∀ᵐ p ∂μ, (z p, ⌊x p.1 p.2 / a⌋) ∈ F) → (angular = true → ∀ (r : ℝ) (q : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U → μ {p | z p = q ∧ ⌊x p.1 p.2 / a⌋ = j ∧ ⌊b p.1 1 / (N ^ (-r))⌋ = k} ≤ ENNReal.ofReal (N ^ η * σ ^ 2 * c * a ^ d * N ^ (-S * r))) → ∃ (n : ℕ) (β t₀ q : ℝ) (A : Fin n → Set α) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), N ^ (-ε) ≤ q ∧ 0 ≤ t₀ ∧ t₀ + q ≤ 1 ∧ σ / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧ (angular = true → N ^ (-ε) ≤ β) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧ (∀ l ∈ A i, ∀ t ∈ Set.Icc t₀ (t₀ + q), |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * a) ∧ ENNReal.ofReal (c * a ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | ∃ i, p.1 ∈ A i}) (fun p => ![⌊p.2 / σ⌋, ⌊y p.1 p.2 / σ⌋])) (fun l t => b l 2 + t * b l 3 + t ^ 2 * b l 4)) (fun l t => b l 0 + t * b l 1)) (N ^ (-m))) (N ^ (-s)))

end Submission.Obl.k4_scalar_mesh_block_reduction
