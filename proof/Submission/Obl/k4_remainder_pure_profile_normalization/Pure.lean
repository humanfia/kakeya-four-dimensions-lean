import Submission.Obl.k4_remainder_pure_profile_normalization.RemainderData
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalizer

/-! The pure part of the exact frozen problem, and its normalization certificate. -/
set_option linter.unusedVariables false

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter

def PureProblem (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ)
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
  True) (fun k γ => ((ν k γ).prod MeasureTheory.volume).restrict (E k γ))


def AngularProblem (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence)
    (P : (k : ℕ) → Fin (W k) → Test)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → JointObservation → ENNReal) : Prop :=
  (fun μ : (k : ℕ) → Fin (W k) → Measure Incidence =>
  (∀ u τ : ℝ, 0 < u → u ≤ η * L → 0 < τ → ∃ c : ℝ, 0 < c ∧
  ∀ᶠ k in Filter.atTop, (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ) {p | ENNReal.ofReal (N k ^ (-f L - S * u + τ)) < G k γ u ((fun p : ((ℕ × (Fin 6 → ℝ)) × ℝ) => ((obs (B k γ) (δ (N k) L)) p, fun j : Fin 2 => ⌊(v p.1) j / (δ (N k) u)⌋)) p)}) ≤ ENNReal.ofReal (N k ^ (-c)))) (fun k γ => ((ν k γ).prod volume).restrict (E k γ))


def Data.PureValid (p : Data) : Prop :=
  PureProblem p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G

def Data.AngularValid (p : Data) : Prop :=
  AngularProblem p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G

theorem Data.valid_iff_pure_angular (p : Data) :
    p.Valid ↔ p.PureValid ∧ p.AngularValid := by
  simp only [Data.Valid, Data.PureValid, Data.AngularValid,
    Problem, PureProblem, AngularProblem, and_true]
  tauto

structure PureRemainder {p : Data} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) (cap : ℝ) where
  K : ℕ → ℝ
  E : (k : ℕ) → Fin (s.atlas k).C → Set Incidence
  f : ℝ → ℝ
  g : (k : ℕ) → Fin (s.atlas k).C → ℝ → Observation → ENNReal
  G : (k : ℕ) → Fin (s.atlas k).C → ℝ → JointObservation → ENNReal
  valid : (s.remainingData cap K E f g G).PureValid
  event_subset : ∀ k c, E k c ⊆ (s.atlas k).system.normEventOf c
  prior_positive : ∀ k c,
    0 < (p.ν (s.index k) ((s.atlas k).γ c) ((s.atlas k).A c)).toReal
  normalizer_subpower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
    ((s.atlas k).system.normZ (p.ω (s.index k)) (p.ν (s.index k)))⁻¹ ≤
      p.N (s.index k) ^ ε
  terminal_comparison : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ c,
    p.N (s.index k) ^ (-p.f p.L) * |((s.atlas k).Q c).det| ≤
      p.N (s.index k) ^ ε *
        (p.ν (s.index k) ((s.atlas k).γ c) ((s.atlas k).A c)).toReal *
        p.N (s.index k) ^ (-f (p.L - r))

end Submission.Obl.k4_remainder_pure_profile_normalization
