import Submission.Obl.k4_unbounded_width_exclusion.ExtremalSequence
import Submission.Obl.k4_unbounded_width_exclusion.Horizon
import Submission.Obl.k4_unbounded_width_exclusion.ScalarGreedy
import Submission.Obl.k4_unbounded_width_exclusion.CoefficientBins
import Submission.Obl.k4_unbounded_width_exclusion.NativeCorrection
import Submission.Obl.k4_unbounded_width_exclusion.PosteriorPair
import Submission.Obl.k4_unbounded_width_exclusion.ScalarFormat
import Submission.Obl.k4_unbounded_width_exclusion.QuadraticPolynomial

/-! Concrete mathematical interfaces for the Section 10 decomposition.
Every proposed child type expands these definitions into Mathlib-only local
bindings. No definition here asserts a theorem. -/

noncomputable section

namespace Submission.Obl.k4_unbounded_width_exclusion

/-- Binning a successful pair of chart occurrences preserves the whole affine
normal motion, as well as its terminal-observation list. -/
def PairedFullTimeBinning : Prop :=
  ∃ C : ℕ, 2 ≤ C ∧
  ∀ (α : Type) [MeasurableSpace α]
    (ν : MeasureTheory.Measure α) (E : Set (α × ℝ))
    (b v : α → EuclideanSpace ℝ (Fin 2)) (n : ℕ)
    (normal : Fin n → EuclideanSpace ℝ (Fin 2))
    (intercept speed : Fin n → ℝ) (tag : α × ℝ → Fin n)
    (O : α × ℝ → EuclideanSpace ℝ (Fin 3) × ℤ)
    (lst : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin n))
    (K H g : ℝ),
    MeasureTheory.IsProbabilityMeasure ν → MeasurableSet E →
    E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → Measurable b → Measurable v →
    Measurable tag → Measurable O →
    (∀ i, ‖normal i‖ = 1 ∧ |intercept i| + |speed i| ≤ K) →
    (∀ o, ((lst o).card : ℝ) ≤ K) →
    (∀ i, MeasurableSet {o | i ∈ lst o}) →
    (∀ p ∈ E, tag p ∈ lst (O p) ∧ ‖b p.1‖ + ‖v p.1‖ ≤ K ∧
      |inner ℝ (normal (tag p)) (b p.1) - intercept (tag p)| ≤ K * g ∧
      |inner ℝ (normal (tag p)) (v p.1) - speed (tag p)| ≤ K * g) →
    2 ≤ K → (C : ℝ) * K ^ 2 ≤ H → 0 < g → g * H ^ 2 ≤ 1 →
    (fun (μ : MeasureTheory.Measure (α × ℝ))
       (pair : MeasureTheory.Measure (α × (ℝ × ℝ))) (bin : Fin n → Fin 4 → ℤ) =>
     0 < μ Set.univ →
     pair {p | (p.1, p.2.1) ∈ E ∧ (p.1, p.2.2) ∈ E ∧
       g * H < min
         ‖normal (tag (p.1, p.2.1)) - normal (tag (p.1, p.2.2))‖
         ‖normal (tag (p.1, p.2.1)) + normal (tag (p.1, p.2.2))‖} ≤
       ENNReal.ofReal ((μ.real Set.univ) ^ 2 / 4) →
     ∃ (t₀ : ℝ) (m : ℕ) (rep : Fin m → Fin n) (A : Fin m → Set α)
       (L : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin m)),
       t₀ ∈ Set.Icc (0 : ℝ) 1 ∧
       (m : ℝ) ≤ ((C : ℝ) * K / (g * H ^ 2)) ^ C ∧
       Function.Injective (fun i => bin (rep i)) ∧
       (∀ i, A i = {l | (l, t₀) ∈ E ∧ bin (tag (l, t₀)) = bin (rep i)}) ∧
       (∀ i, MeasurableSet (A i)) ∧
       (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
       (∀ i l, l ∈ A i → ∀ t ∈ Set.Icc (0 : ℝ) 1,
         |inner ℝ (normal (rep i)) (b l + t • v l) -
           intercept (rep i) - t * speed (rep i)| ≤ (C : ℝ) * K * (g * H ^ 2)) ∧
       (∀ o, ((L o).card : ℝ) ≤ (C : ℝ) * K) ∧
       (∀ i, MeasurableSet {o | i ∈ L o}) ∧
       ENNReal.ofReal ((μ.real Set.univ) ^ 2 / 4) ≤
         μ {p | ∃ i, p.1 ∈ A i ∧ i ∈ L (O p)})
      ((ν.prod MeasureTheory.volume).restrict E)
      (ν.prod (MeasureTheory.volume.prod MeasureTheory.volume))
      (fun i => ![⌊normal i 0 / (g * H ^ 2)⌋, ⌊normal i 1 / (g * H ^ 2)⌋,
         ⌊intercept i / (g * H ^ 2)⌋, ⌊speed i / (g * H ^ 2)⌋])

/-- Only the real oscillation consequence of stable native graphs is needed
for the projected support count. Hidden coordinates and polynomial coefficients
need no a priori subpower bound. -/
def StableNativeOscillation : Prop :=
  ∀ A : ℕ, ∃ C : ℕ, 1 ≤ C ∧
  ∀ (K a : ℝ) (P S : MvPolynomial (Fin 4) ℝ)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 4))),
    2 ≤ K → 0 < a → a ≤ 1 → P.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
    MeasureTheory.IsProbabilityMeasure μ →
    (fun base : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 3) =>
     MeasureTheory.Measure.map base μ ≤ ENNReal.ofReal K • MeasureTheory.volume →
     (∀ᵐ p ∂μ, ‖base p‖ ≤ K ∧
       |MvPolynomial.eval (fun i => p i) P| ≤ K * a ∧
       K⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) P)| ∧
       |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K ∧
       |MvPolynomial.eval (fun i => p i)
         (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K / a ∧
       |MvPolynomial.eval (fun i => p i) S| ≤ K ∧
       |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3 : Fin 4) S)| ≤ K ∧
       |MvPolynomial.eval (fun i => p i)
         (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) S))| ≤ K) →
     ∃ (n : ℕ) (E : Fin n → Set (EuclideanSpace ℝ (Fin 4))),
       (n : ℝ) ≤ K ^ C ∧ (∀ i, MeasurableSet (E i)) ∧
       (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
       μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹) ∧
       ∀ i p, p ∈ E i → ∀ q, q ∈ E i →
         |MvPolynomial.eval (fun j => p j) S - MvPolynomial.eval (fun j => q j) S| ≤
           K ^ C * (a + ‖base p - base q‖))
      (fun p => WithLp.toLp 2 ![p 0, p 1, p 2])

/-- Continuous base caps supplement the scalar mesh bounds. These are what
control the index/base marginals in posterior matching. -/
def ProjectedScalarLaw
    (N η d s m S U : ℝ) (ν : MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (μ : MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ) : Prop :=
  ScalarAdmissible N η d s m 1 S U 1 ν b μ ∧
  ∀ (r : ℝ) (j : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
    0 ≤ r → r ≤ s → MeasurableSet E →
    μ {p | WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∈ E ∧
      ⌊scalarX (b p.1) p.2 / (N ^ (-r))⌋ = j} ≤
      ENNReal.ofReal (N ^ η * (N ^ (-r)) ^ d) * MeasureTheory.volume E

/-- A finite recovery statement, with an arbitrary specified original observation.
Output assignments are geometric sets in the five scalar coefficients. -/
def FixedBudgetQuadraticRecovery : Prop :=
  ∀ d s m S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < 1 → s < m → 0 < S → 0 < U → U < m →
  ∃ c : ℝ, 0 < c ∧ c < min s 1 ∧ ∃ M D : ℕ, 1 ≤ M ∧
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
  ∀ N : ℝ, N₀ ≤ N →
  ∀ (ν : MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (μ : MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ)
    (O : ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ)
    (base : (EuclideanSpace ℝ (Fin 3) × ℤ) → EuclideanSpace ℝ (Fin 2))
    (signal : (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ),
    ProjectedScalarLaw N η d s m S U ν μ b →
    ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ →
    Measurable O → Measurable base → Measurable signal →
    (∀ᵐ p ∂μ, base (O p) = WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∧
      |scalarX (b p.1) p.2 - signal (O p)| ≤ N ^ (-1 + η)) →
    ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
      (A : Fin n → Set (Fin 5 → ℝ))
      (lst : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin n)),
      (n : ℝ) ≤ N ^ (d * s + ε) ∧
      (∀ i, (P i).totalDegree ≤ 2 ∧ (∀ e, |(P i).coeff e| ≤ N ^ ε) ∧
        MeasurableSet (A i) ∧ fmt 5 (N ^ M) D (A i) ∧
        ∀ z ∈ A i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |scalarX z t - MvPolynomial.eval ![t, scalarY z t] (P i)| ≤ N ^ (-c)) ∧
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      (∀ o, (lst o).card ≤ M) ∧
      (∀ i, MeasurableSet {o | i ∈ lst o}) ∧
      ENNReal.ofReal (1 / 2 : ℝ) * μ Set.univ ≤
        μ {p | ∃ i, b p.1 ∈ A i ∧ i ∈ lst (O p)}

/-- A genuine known atlas: all geometric chart clauses remain, and a terminal
list replaces the true floor only in this separate predicate. -/
def known
    (N K : ℕ → ℝ) (L : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (B : (k : ℕ) → Fin (W k) → ℝ) (r h : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
    ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧
    ∃ (T C : ℕ) (γ : Fin C → Fin (W k)) (j : Fin C → Fin (2 ^ T))
      (c u : Fin C → EuclideanSpace ℝ (Fin 2))
      (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
      (R : Fin C → MvPolynomial (Fin 4) ℝ)
      (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
      (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)),
      (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (C : ℝ) ≤ N k ^ M ∧
      (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
      (∀ w o, ((lst w o).card : ℝ) ≤ κ) ∧
      (∀ b, chart (N k) M D κ T ((j b : ℕ) : ℝ) r (B k (γ b)) (E k (γ b))
        (c b) (u b) (Q b) (R b) (A b) (F b)
        (∀ p ∈ F b, b ∈ lst (γ b) (obs (B k (γ b)) (δ (N k) L) p))) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) *
        ((ν k (γ b)).prod MeasureTheory.volume) (F b)

/-- The known-atlas convention in the reused local-remainder transfer o147.
It omits the harmless K<=kappa restoration, and carries an unused profile. -/
def weakKnown
    (N K : ℕ → ℝ) (L : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ) (r h : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
    ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ N k ^ ε ∧
    ∃ (T C : ℕ) (γ : Fin C → Fin (W k)) (j : Fin C → Fin (2 ^ T))
      (c u : Fin C → EuclideanSpace ℝ (Fin 2))
      (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
      (R : Fin C → MvPolynomial (Fin 4) ℝ)
      (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
      (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (lst : Fin (W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)),
      (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (C : ℝ) ≤ N k ^ M ∧
      (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
      (∀ w o, ((lst w o).card : ℝ) ≤ κ) ∧
      (∀ b, chart (N k) M D κ T ((j b : ℕ) : ℝ) r (B k (γ b)) (E k (γ b))
        (c b) (u b) (Q b) (R b) (A b) (F b)
        (∀ p ∈ F b, b ∈ lst (γ b) (obs (B k (γ b)) (δ (N k) L) p))) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) *
        ((ν k (γ b)).prod MeasureTheory.volume) (F b)

/-- The exact conclusion of o147, stated using the named predicates here. -/
def LocalRemainderTransfer : Prop :=
  ∀ N K L d S η W ω ν E P B f g G,
    prob N K L d S η W ω ν E P B f g G →
    ∀ r h q : ℝ, 0 ≤ r → r < L → 0 < q → q < 1 →
    (∀ s : ℝ, r ≤ s → s ≤ L → f L - f s ≤ q * (L - s)) →
    weakKnown N K L W ω ν E B f r h →
    ∃ N₂ K₂ W₂ ω₂ ν₂ E₂ P₂ B₂ f₂ g₂ G₂,
      prob N₂ K₂ (L - r) q S η W₂ ω₂ ν₂ E₂ P₂ B₂ f₂ g₂ G₂ ∧
      H N K L W ω ν E B f ≤ h + H N₂ K₂ (L - r) W₂ ω₂ ν₂ E₂ B₂ f₂

/-- Horizon closure through a known atlas. The valid residual problem retains
its cap dimension, angular parameters and remaining depth length. The e-loss
allows independent exact subsequences and arbitrarily small homogenization losses. -/
def KnownAtlasComposition : Prop :=
  ∀ N K L d S η W ω ν E P B f g G,
    prob N K L d S η W ω ν E P B f g G →
    ∀ r h : ℝ, 0 ≤ r → r < L → known N K L W ω ν E B r h →
    ∀ e : ℝ, 0 < e →
    ∃ N' K' L' d' W' ω' ν' E' P' B' f' g' G',
      prob N' K' L' d' S η W' ω' ν' E' P' B' f' g' G' ∧
      L' = L - r ∧ d' = d ∧
      H N K L W ω ν E B f ≤ h + H N' K' L' W' ω' ν' E' B' f' + e

/-- The universal nearby rate bound excludes a fixed positive depth gain with
less than half its critical time cost. -/
def KnownAtlasExclusion : Prop :=
  ∀ ds kr S η : ℝ, 0 < S → 0 < η → es ds kr S η →
  ∀ c : ℝ, 0 < c → c < 1 → ∃ a : ℝ, 0 < a ∧
  ∀ N K d W ω ν E P B f g G,
    prob N K 1 d S η W ω ν E P B f g G → d < ds + a →
    kr - a < H N K 1 W ω ν E B f → ¬ known N K 1 W ω ν E B c (kr * c / 2)

/-- The remaining geometric reduction uses the four explicit local tools.
Neither scalar mesh projection nor two-color matching is hidden in this type. -/
def GeometricPacketReduction : Prop :=
  PairedFullTimeBinning → StableNativeOscillation → FixedBudgetQuadraticRecovery →
  KnownAtlasExclusion → InitialHorizonBound →
  ∀ ds kr S η : ℝ, 0 < S → 0 < η → es ds kr S η → bw ds kr S η

/-- The conclusion of the reused local algebraic matching obligation o112. -/
def LocalAlgebraicMatching : Prop :=
  (∀ D : ℕ, ∀ d₀ : ℝ, 0 ≤ d₀ → d₀ < 1 → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ → ∀ n₁ n₂ : ℕ, ∀ (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ) (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) (P₁ : Fin n₁ → MvPolynomial (Fin 4) ℂ) (P₂ : Fin n₂ → MvPolynomial (Fin 4) ℂ) (f₀ : EuclideanSpace ℝ (Fin 3) → ℂ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))), (fun emb : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3) => (n₁ : ℝ) ≤ R ^ (d₀ + ε) → (n₂ : ℝ) ≤ R ^ (d₀ + ε) → (∀ i, P₁ i ≠ 0 ∧ (P₁ i).totalDegree ≤ D ∧ DifferentiableOn ℂ (f₁ i) (Metric.ball 0 4) ∧ (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f₁ i z)) (P₁ i) = 0) ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f₁ i (emb x)).im = 0 ∧ ‖f₁ i (emb x) - f₀ x‖ ≤ M * R ^ ε) → (∀ i, P₂ i ≠ 0 ∧ (P₂ i).totalDegree ≤ D ∧ DifferentiableOn ℂ (f₂ i) (Metric.ball 0 4) ∧ (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f₂ i z)) (P₂ i) = 0) ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f₂ i (emb x)).im = 0 ∧ ‖f₂ i (emb x) - f₀ x‖ ≤ M * R ^ ε) → (∀ i, 0 ≤ π₁ i) → (∀ i, 0 ≤ π₂ i) → (∑ i, π₁ i) = 1 → (∑ i, π₂ i) = 1 → ENNReal.ofReal (R ^ (-ε)) ≤ μ Set.univ → μ Set.univ ≤ 1 → (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₁ i) * MeasureTheory.volume U) → (∀ (i : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U → μ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (R ^ ε * π₂ i) * MeasureTheory.volume U) → ¬ μ {p | ‖p.2‖ ≤ (1 : ℝ) / 2 ∧ ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ M * R ^ (-1 + ε) ∧ ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ (1 : ℝ) / 2 ∧ M * R ^ (-ε) ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖}ᶜ = 0) (fun x => WithLp.toLp 2 (fun i => (x i : ℂ))))

end Submission.Obl.k4_unbounded_width_exclusion
