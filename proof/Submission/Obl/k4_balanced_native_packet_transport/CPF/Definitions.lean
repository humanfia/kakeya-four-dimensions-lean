/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/Definitions.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Mathlib
import ChallengeDeps

/-! The version-2 problem and chart predicates, expanded exactly as in o105.
These names package the immediately applied functions in the frozen statement.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Filter
open scoped ENNReal

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Observation := EuclideanSpace ℝ (Fin 3) × ℤ
abbrev JointObservation := Observation × (Fin 2 → ℤ)
abbrev Spatial := EuclideanSpace ℝ (Fin 2)
abbrev Frame := Matrix (Fin 2) (Fin 2) ℝ
abbrev Test := MvPolynomial (Fin 4) ℝ

def x (l : Trajectory) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

def y (l : Trajectory) (t : ℝ) : Spatial :=
  WithLp.toLp 2 ![(x l t) 1, (x l t) 2]

def v (l : Trajectory) : Spatial := WithLp.toLp 2 ![l.2 3, l.2 4]

noncomputable def δ (N r : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

noncomputable def obs (B a : ℝ) (p : Incidence) : Observation :=
  (WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2], ⌊B * (x p.1 p.2) 3 / a⌋)

def fmt (n : ℕ) (H : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) : Prop :=
  ∃ m₀ : ℕ, (m₀ : ℝ) ≤ H ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin n) ℝ,
    (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool,
    ∀ x₀, x₀ ∈ A ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true

/-- A single chart, with a parameter for its final floor or list condition. -/
def Chart (Nk : ℝ) (M D : ℕ) (κ : ℝ) (T : ℕ) (j r Bv : ℝ)
    (Ev : Set Incidence) (c u : Spatial) (Q : Frame) (R : Test)
    (A : Set Trajectory) (F : Set Incidence) (ex : Prop) : Prop :=
  Matrix.det Q ≠ 0 ∧
  ‖c‖ + ‖u‖ ≤ Nk ^ M ∧
  (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ Nk ^ M ∧
  (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧
  R.totalDegree ≤ 2 ∧
  (∀ e, |R.coeff e| ≤ Nk ^ M) ∧
  MeasurableSet A ∧
  MeasurableSet F ∧
  (∀ i, fmt 6 (Nk ^ M) D {x | (i, x) ∈ A} ∧
  fmt 7 (Nk ^ M) D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) ∧
  (∀ l ∈ A, (l.1 : ℝ) ≤ Nk ^ M ∧
  (∀ e, |l.2 e| ≤ Nk ^ M) ∧
  ∀ t ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T), ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ ∧
  |MvPolynomial.eval (x l t) R| ≤ κ * δ Nk r ∧
  |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) R)| ≤ κ * Bv ∧
  |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) R))| ≤ κ * Bv ^ 2 / δ Nk r) ∧
  (∀ p ∈ F, p ∈ Ev ∧
  p.1 ∈ A ∧
  p.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) ∧
  Bv / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) R)|) ∧
  ex

/-- All the hypotheses of a tempered homogeneous cap-class problem. -/
def Problem (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence)
    (P : (k : ℕ) → Fin (W k) → Test)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → JointObservation → ENNReal) : Prop :=
  (∀ k, 2 ≤ N k) ∧
  Filter.Tendsto N Filter.atTop Filter.atTop ∧
  ((∀ k, 1 ≤ K k) ∧
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧
  0 < L ∧
  0 < d ∧
  d < 1 ∧
  0 < S ∧
  0 < η ∧
  (fun μ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) => (∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧
  (∀ γ, 0 ≤ ω k γ) ∧
  (∑ γ, ω k γ) = 1 ∧
  (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧
  0 < B k γ ∧
  B k γ ≤ N k ^ M ∧
  (B k γ)⁻¹ ≤ N k ^ M ∧
  (P k γ).totalDegree ≤ 2 ∧
  (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧
  (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧
  ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧
  c j ≤ N k ^ M ∧
  (i j : ℝ) ≤ N k ^ M ∧
  (fmt 6 (N k ^ M) D (A j)) ∧
  (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧
  ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧
  MeasurableSet (E k γ) ∧
  E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
  (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧
  ∀ e, |p.1.2 e| ≤ N k ^ M) ∧
  (∀ i, (fmt 7 (N k ^ M) D ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}))) ∧
  (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(y l t)‖ + ‖(v l)‖ ≤ K k ∧
  |MvPolynomial.eval (x l t) (P k γ)| ≤ K k ∧
  |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧
  |MvPolynomial.eval (x l t) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧
  (∀ᵐ p ∂(μ k γ), B k γ / K k ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧
  ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) Set.univ) ∧
  (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧
  MeasureTheory.Measure.map (obs (B k γ) (δ (N k) r)) (μ k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (g k γ r)) ∧
  (∀ k γ u, 0 < u → u ≤ η * L → Measurable (G k γ u) ∧
  MeasureTheory.Measure.map (fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) (μ k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (G k γ u)) ∧
  (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L → 0 ≤ f s - f r ∧
  f s - f r ≤ s - r) ∧
  (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧
  ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | g k γ r ((obs (B k γ) (δ (N k) r)) p) < ENNReal.ofReal (N k ^ (-f r - τ)) ∨ ENNReal.ofReal (N k ^ (-f r + τ)) < g k γ r ((obs (B k γ) (δ (N k) r)) p)}) ≤ ENNReal.ofReal (N k ^ (-c))) ∧
  (∀ r : ℝ, 0 ≤ r → r ≤ L → f L - f r ≤ d * (L - r)) ∧
  (∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧
  ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c)))) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ))

end Submission.Obl.k4_balanced_native_packet_transport.CPF

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Filter

/-- The numerical and measure data of one exact problem. -/
structure Data where
  N : ℕ → ℝ
  K : ℕ → ℝ
  L : ℝ
  d : ℝ
  S : ℝ
  η : ℝ
  W : ℕ → ℕ
  ω : (k : ℕ) → Fin (W k) → ℝ
  ν : (k : ℕ) → Fin (W k) → Measure Trajectory
  E : (k : ℕ) → Fin (W k) → Set Incidence
  P : (k : ℕ) → Fin (W k) → Test
  B : (k : ℕ) → Fin (W k) → ℝ
  f : ℝ → ℝ
  g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal
  G : (k : ℕ) → Fin (W k) → ℝ → JointObservation → ENNReal

def Data.Valid (p : Data) : Prop :=
  Problem p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G

/-- A finite collection of charts, before imposing geometric or mass conditions. -/
structure Atlas (p : Data) (k : ℕ) where
  κ : ℝ
  T : ℕ
  C : ℕ
  γ : Fin C → Fin (p.W k)
  j : Fin C → Fin (2 ^ T)
  c : Fin C → Spatial
  u : Fin C → Spatial
  Q : Fin C → Frame
  R : Fin C → Test
  A : Fin C → Set Trajectory
  F : Fin C → Set Incidence

def Atlas.Separated {p : Data} {k : ℕ} (a : Atlas p k) : Prop :=
  ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b')

noncomputable def Atlas.mass {p : Data} {k : ℕ} (a : Atlas p k) : ENNReal :=
  ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b)

/-- The actual floor is part of every chart; it is never replaced by a list condition. -/
def Atlas.TrueAt {p : Data} {k : ℕ} (a : Atlas p k) (M D : ℕ) (r : ℝ) : Prop :=
  (a.C : ℝ) ≤ p.N k ^ M ∧ a.Separated ∧
  (∀ b, Chart (p.N k) M D a.κ a.T (a.j b : ℝ) r (p.B k (a.γ b)) (p.E k (a.γ b))
    (a.c b) (a.u b) (a.Q b) (a.R b) (a.A b) (a.F b)
    (ENNReal.ofReal (p.N k ^ (-p.f r) * |Matrix.det (a.Q b)| /
      ((2 : ℝ) ^ a.T * a.κ)) ≤ ((p.ν k (a.γ b)).prod volume) (a.F b))) ∧
  ENNReal.ofReal a.κ⁻¹ ≤ a.mass

/-- A true terminal system at one fixed tolerance and sample. -/
def TerminalAt (p : Data) (M D : ℕ) (h ε : ℝ) (k : ℕ) : Prop :=
  ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
    (2 : ℝ) ^ a.T ≤ p.N k ^ h ∧ a.TrueAt M D p.L

/-- Fixed format bounds precede the tolerance and the frequently chosen samples. -/
def Terminal (p : Data) (h : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, TerminalAt p M D h ε k

/-- The initial horizon input from Proposition 2.16. -/
def InitialHorizon : Prop :=
  ∀ p : Data, p.Valid → ∀ h : ℝ, p.L < h → Terminal p h

end Submission.Obl.k4_balanced_native_packet_transport.CPF
