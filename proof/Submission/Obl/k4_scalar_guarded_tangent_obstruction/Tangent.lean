import Submission.Obl.k4_scalar_guarded_tangent_obstruction.Defs

namespace Submission.Obl.k4_scalar_guarded_tangent_obstruction

open MeasureTheory Filter
open scoped Topology

/-- Scalar tangent data with the full assigned priors and fixed palettes. -/
structure TangentData where
  N : ℕ → ℝ
  K : ℕ → ℝ
  d : ℝ
  κ : ℝ
  S : ℝ
  W : ℕ → ℕ
  weight : (k : ℕ) → Fin (W k) → ℝ
  prior : (k : ℕ) → Fin (W k) → Measure Coeff
  incidence : (k : ℕ) → Fin (W k) → Measure Incidence
  palette : (k : ℕ) → Fin (W k) → Measure ℝ
  T : ℕ → ℝ → ℕ
  n : ℕ → ℝ → ℕ
  world : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)
  block : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)
  assignment : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set Coeff
  u : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ
  v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ
  graph : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ

noncomputable def baseBin (N r : ℝ) (p : Incidence) (e : Fin 2) : ℤ :=
  ⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / (N ^ (-r))⌋

noncomputable def hiddenBin (N s : ℝ) (p : Incidence) : ℤ :=
  ⌊x p.1 p.2 / (N ^ (-s))⌋

noncomputable def velocityBin (N b : ℝ) (v : ℝ) : ℤ :=
  ⌊v / (N ^ (-b))⌋

namespace TangentData

def Global (a : TangentData) : Prop :=
  ∀ k, (∀ g, 0 ≤ a.weight k g) ∧ (∑ g, a.weight k g) = 1 ∧
    (∀ g, IsProbabilityMeasure (a.prior k g) ∧ IsProbabilityMeasure (a.palette k g) ∧
      (∀ᵐ l ∂a.prior k g, ∀ e, |l.2 e| ≤ a.K k) ∧
      a.incidence k g ≤ ENNReal.ofReal (a.K k) • ((a.prior k g).prod volume) ∧
      a.incidence k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧
    ENNReal.ofReal ((a.K k)⁻¹) ≤
      ∑ g, ENNReal.ofReal (a.weight k g) * a.incidence k g Set.univ

def Caps (a : TangentData) : Prop :=
  ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ (g : Fin (a.W k)) (r s b : ℝ),
    R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
    (∀ c : ℤ, a.palette k g {v | velocityBin (a.N k) b v = c} ≤
      ENNReal.ofReal (a.K k * a.N k ^ (-a.S * b))) ∧
    (∀ (q : Fin 2 → ℤ) (c : ℤ), a.incidence k g
      {p | baseBin (a.N k) r p = q ∧ hiddenBin (a.N k) s p = c} ≤
      ENNReal.ofReal (a.K k * a.N k ^ (-2 * r - a.d * s))) ∧
    (∀ (q : Fin 2 → ℤ) (c e : ℤ), a.incidence k g
      {p | baseBin (a.N k) r p = q ∧ hiddenBin (a.N k) s p = c ∧
        velocityBin (a.N k) b (p.1.2 1) = e} ≤
      ENNReal.ofReal (a.K k * a.N k ^ (-2 * r - a.d * s)) *
        a.palette k g {v | velocityBin (a.N k) b v = e})

def Charts (a : TangentData) : Prop :=
  ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
    a.N k ^ (a.κ * s) / a.K k ≤ (2 : ℝ) ^ a.T k s ∧
    (2 : ℝ) ^ a.T k s ≤ a.K k * a.N k ^ (a.κ * s) ∧
    (∀ i, MeasurableSet (a.assignment k s i)) ∧
    (∀ i i', i ≠ i' → a.world k s i = a.world k s i' →
      a.block k s i = a.block k s i' → Disjoint (a.assignment k s i) (a.assignment k s i')) ∧
    (∀ i, ENNReal.ofReal (a.N k ^ (-a.d * s) / (a.K k * (2 : ℝ) ^ a.T k s)) ≤
        a.prior k (a.world k s i) (a.assignment k s i) ∧
      a.prior k (a.world k s i) (a.assignment k s i) ≤
        ENNReal.ofReal (a.K k * a.N k ^ (-a.d * s) / (2 : ℝ) ^ a.T k s) ∧
      ENNReal.ofReal ((a.K k * (2 : ℝ) ^ a.T k s)⁻¹) *
        a.prior k (a.world k s i) (a.assignment k s i) ≤
        a.incidence k (a.world k s i) (a.assignment k s i ×ˢ I (a.T k s) (a.block k s i)) ∧
      |a.u k s i| + |a.v k s i| ≤ a.K k ∧ (a.graph k s i).totalDegree ≤ 2 ∧
      (∀ t ∈ I (a.T k s) (a.block k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2,
        |MvPolynomial.eval ![t, a.u k s i + t * a.v k s i + w / (2 : ℝ) ^ a.T k s]
          (a.graph k s i)| ≤ a.K k) ∧
      (∀ l ∈ a.assignment k s i, ∀ t ∈ I (a.T k s) (a.block k s i),
        |y l t - a.u k s i - t * a.v k s i| ≤ a.K k / (2 : ℝ) ^ a.T k s ∧
        |x l t - MvPolynomial.eval ![t, y l t] (a.graph k s i)| ≤
          a.K k * a.N k ^ (-s))) ∧
    (∀ g : Fin (a.W k), a.incidence k g
      {p | ∃ i, a.world k s i = g ∧ p.1 ∈ a.assignment k s i ∧
        p.2 ∈ I (a.T k s) (a.block k s i)}ᶜ = 0)

structure Valid (a : TangentData) : Prop where
  resolution : ∀ k, 2 ≤ a.N k
  resolution_tendsto : Tendsto a.N atTop atTop
  loss : (∀ k, 1 ≤ a.K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a.K k ≤ a.N k ^ ε
  d_nonneg : 0 ≤ a.d
  d_lt_one : a.d < 1
  κ_pos : 0 < a.κ
  κ_le_one : a.κ ≤ 1
  S_pos : 0 < a.S
  global : a.Global
  caps : a.Caps
  charts : a.Charts

def Candidate (a : TangentData) (R ε : ℝ) (k : ℕ) : Prop :=
  ∃ (s c : ℝ) (i : Fin (a.n k s)) (P : MvPolynomial (Fin 2) ℝ),
    R⁻¹ ≤ s ∧ s ≤ R ∧ R⁻¹ ≤ c ∧ c ≤ R ∧ P.totalDegree ≤ 2 ∧
    (∀ b, |P.coeff b| ≤ a.N k ^ R) ∧
    ENNReal.ofReal (a.N k ^ (-a.d * c - ε) / (2 : ℝ) ^ a.T k s) *
      a.prior k (a.world k s i) (a.assignment k s i) ≤
      a.incidence k (a.world k s i)
        {p | p.1 ∈ a.assignment k s i ∧ p.2 ∈ I (a.T k s) (a.block k s i) ∧
          ∀ t ∈ I (a.T k s) (a.block k s i),
            |x p.1 t - MvPolynomial.eval ![t, y p.1 t] P| ≤
              a.N k ^ ε * a.N k ^ (-s - c)}

theorem Valid.improvement {a : TangentData} (ha : a.Valid) (hSTI : STI) :
    ∃ R : ℝ, 1 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, a.Candidate R ε k := by
  exact hSTI a.N a.K ha.resolution ha.resolution_tendsto ha.loss
    a.d a.κ a.S ha.d_nonneg ha.d_lt_one ha.κ_pos ha.κ_le_one ha.S_pos
    a.W a.weight a.prior a.incidence a.palette a.T a.n a.world a.block a.assignment
    a.u a.v a.graph ha.global ha.caps ha.charts

end TangentData

end Submission.Obl.k4_scalar_guarded_tangent_obstruction
