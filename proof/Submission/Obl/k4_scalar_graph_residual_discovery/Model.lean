/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file Model.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Table
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.OriginalMarking
import Submission.Lib.K4ContinuousKakeya.Continuous

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

abbrev ScalarLine := ℕ × (Fin 5 → ℝ)
abbrev ScalarIncidence := ScalarLine × ℝ

/-- The arrays and parameters of the frozen obligation, with no hypotheses added. -/
structure ScalarData where
  N : ℕ → ℝ
  K : ℕ → ℝ
  d : ℝ
  κ : ℝ
  S : ℝ
  W : ℕ → ℕ
  ω : (k : ℕ) → Fin (W k) → ℝ
  ν : (k : ℕ) → Fin (W k) → Measure ScalarLine
  ρ : (k : ℕ) → Fin (W k) → Measure ScalarIncidence
  π : (k : ℕ) → Fin (W k) → Measure ℝ
  T : ℕ → ℝ → ℕ
  n : ℕ → ℝ → ℕ
  γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)
  j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)
  A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set ScalarLine
  u : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ
  v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ
  F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ

noncomputable section

def scalarY (l : ScalarLine) (t : ℝ) : ℝ := l.2 0 + t * l.2 1

def scalarX (l : ScalarLine) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

def timeBlock (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

def baseCode (B r : ℝ) (p : ScalarIncidence) (e : Fin 2) : ℤ :=
  ⌊(![p.2, scalarY p.1 p.2] : Fin 2 → ℝ) e / (B ^ (-r))⌋

namespace ScalarData

variable (D : ScalarData)

def phys (k : ℕ) (r : ℝ) (p : ScalarIncidence) (e : Fin 3) : ℤ :=
  ⌊(![p.2, scalarY p.1 p.2, scalarX p.1 p.2] : Fin 3 → ℝ) e / (D.N k ^ (-r))⌋

def coeff (k : ℕ) (r : ℝ) (l : ScalarLine) (e : Fin 5) : ℤ :=
  ⌊l.2 e / (D.N k ^ (-r))⌋

def vel (k : ℕ) (r : ℝ) (c : ℤ) : Set ℝ := {v | (⌊v / (D.N k ^ (-r))⌋ : ℤ) = c}

def rowbin (k : ℕ) (r : ℝ) (v : Fin 2 → ℝ) (e : Fin 2) : ℤ :=
  ⌊v e / (D.N k ^ (-r))⌋

def Parameters : Prop :=
  (∀ k, 2 ≤ D.N k) ∧ Tendsto D.N atTop atTop ∧ Subpower D.N D.K ∧
    0 ≤ D.d ∧ D.d < 1 ∧ 0 < D.κ ∧ D.κ ≤ 1 ∧ 0 < D.S

def base  : Prop :=
  (∀ k, (∀ g, 0 ≤ D.ω k g) ∧ (∑ g, D.ω k g) = 1 ∧ (∀ g, MeasureTheory.IsProbabilityMeasure (D.ν k g) ∧
  MeasureTheory.IsProbabilityMeasure (D.π k g) ∧ (∀ᵐ l ∂D.ν k g, ∀ e, |l.2 e| ≤ D.K k) ∧ D.ρ k g ≤
  ENNReal.ofReal (D.K k) • ((D.ν k g).prod MeasureTheory.volume) ∧ D.ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ =
  0) ∧ ENNReal.ofReal ((D.K k)⁻¹) ≤ ∑ g, ENNReal.ofReal (D.ω k g) * D.ρ k g Set.univ)

def caps  : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (D.W k)) (r s b : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R →
  R⁻¹ ≤ b → b ≤ R → (∀ c : ℤ, D.π k g {v : ℝ | (⌊v / (D.N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (D.K k *
  D.N k ^ (-D.S * b))) ∧ (∀ (q : Fin 2 → ℤ) (a : ℤ), D.ρ k g {p | baseCode (D.N k) r p = q ∧ (⌊scalarX p.1 p.2
  / (D.N k ^ (-s))⌋ : ℤ) = a} ≤ ENNReal.ofReal (D.K k * D.N k ^ (-2 * r - D.d * s))) ∧ (∀ (q : Fin 2 → ℤ) (a c
  : ℤ), D.ρ k g {p | baseCode (D.N k) r p = q ∧ (⌊scalarX p.1 p.2 / (D.N k ^ (-s))⌋ : ℤ) = a ∧ (⌊p.1.2 1 /
  (D.N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (D.K k * D.N k ^ (-2 * r - D.d * s)) * D.π k g {v : ℝ | (⌊v /
  (D.N k ^ (-b))⌋ : ℤ) = c}))

def packets  : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → D.N k ^ (D.κ * s) / D.K k ≤ (2 : ℝ) ^ D.T
  k s ∧ (2 : ℝ) ^ D.T k s ≤ D.K k * D.N k ^ (D.κ * s) ∧ (∀ i, MeasurableSet (D.A k s i)) ∧ (∀ i i', i ≠ i' →
  D.γ k s i = D.γ k s i' → D.j k s i = D.j k s i' → Disjoint (D.A k s i) (D.A k s i')) ∧ (∀ i, ENNReal.ofReal
  (D.N k ^ (-D.d * s) / (D.K k * (2 : ℝ) ^ D.T k s)) ≤ D.ν k (D.γ k s i) (D.A k s i) ∧ D.ν k (D.γ k s i) (D.A
  k s i) ≤ ENNReal.ofReal (D.K k * D.N k ^ (-D.d * s) / (2 : ℝ) ^ D.T k s) ∧ ENNReal.ofReal ((D.K k * (2 : ℝ)
  ^ D.T k s)⁻¹) * D.ν k (D.γ k s i) (D.A k s i) ≤ D.ρ k (D.γ k s i) (D.A k s i ×ˢ timeBlock (D.T k s) (D.j k s
  i)) ∧ |D.u k s i| + |D.v k s i| ≤ D.K k ∧ (D.F k s i).totalDegree ≤ 2 ∧ (∀ t ∈ timeBlock (D.T k s) (D.j k s
  i), ∀ w ∈ Set.Icc (-2 : ℝ) 2, |MvPolynomial.eval ![t, D.u k s i + t * D.v k s i + w / (2 : ℝ) ^ D.T k s]
  (D.F k s i)| ≤ D.K k) ∧ (∀ l ∈ D.A k s i, ∀ t ∈ timeBlock (D.T k s) (D.j k s i), |scalarY l t - D.u k s i -
  t * D.v k s i| ≤ D.K k / (2 : ℝ) ^ D.T k s ∧ |scalarX l t - MvPolynomial.eval ![t, scalarY l t] (D.F k s i)|
  ≤ D.K k * D.N k ^ (-s))) ∧ (∀ g : Fin (D.W k), D.ρ k g {p | ∃ i, D.γ k s i = g ∧ p.1 ∈ D.A k s i ∧ p.2 ∈
  timeBlock (D.T k s) (D.j k s i)}ᶜ = 0))

def prepData (H : ℕ → ℝ)
    (θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine)
    (E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence) : Prop :=
  Subpower D.N H ∧ ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ D.N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧ (∀ R : ℝ, 1 < R → ∀ᶠ k
  in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (D.W k), ENNReal.ofReal (D.ω k g) * (D.ρ k g).restrict
  (E k g) Set.univ ∧ ∀ g : Fin (D.W k), θ k g ≤ D.ν k g ∧ θ k g Set.univ ≤ 1 ∧ MeasurableSet (E k g) ∧ (∀ p ∈
  E k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H k) ∧ (∀ᵐ l ∂θ k g, ∀ e, |l.2 e| ≤ H k) ∧ ENNReal.ofReal
  ((H k)⁻¹) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ≤ (D.ρ k g).restrict (E k g) ∧ (D.ρ k
  g).restrict (E k g) ≤ ENNReal.ofReal (H k) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ∧ (∀ r :
  ℝ, R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) → Set.Finite {q : Fin 3 → ℤ | (D.ρ k g).restrict (E
  k g) {p | D.phys k r p = q} ≠ 0} ∧ ({q : Fin 3 → ℤ | (D.ρ k g).restrict (E k g) {p | D.phys k r p = q} ≠
  0}.ncard : ℝ) ≤ H k * D.N k ^ ((2 + D.d) * r) ∧ (∀ r₀ : ℝ, R⁻¹ ≤ r₀ → r₀ ≤ r → (∃ m : ℕ, r₀ = (m : ℝ) / (M k
  : ℝ)) → ∀ q₀ : Fin 3 → ℤ, ({q : Fin 3 → ℤ | (D.ρ k g).restrict (E k g) {p | D.phys k r p = q ∧ D.phys k r₀ p
  = q₀} ≠ 0}.ncard : ℝ) ≤ H k * D.N k ^ ((2 + D.d) * (r - r₀))) ∧ (∀ q : Fin 5 → ℤ, (D.ρ k g).restrict (E k g)
  {p | D.coeff k r p.1 = q} ≠ 0 → ENNReal.ofReal (D.N k ^ (-(1 + D.d) * r) / H k) * D.π k g (D.vel k r (q 1))
  ≤ θ k g {l | D.coeff k r l = q} ∧ θ k g {l | D.coeff k r l = q} ≤ ENNReal.ofReal (H k * D.N k ^ (-(1 + D.d)
  * r)) * D.π k g (D.vel k r (q 1))) ∧ (∀ (q : Fin 3 → ℤ) (c : ℤ), ({b : Fin 5 → ℤ | (D.ρ k g).restrict (E k
  g) {p | D.phys k r p = q ∧ D.coeff k r p.1 1 = c ∧ D.coeff k r p.1 = b} ≠ 0}.ncard : ℝ) ≤ H k)) ∧ (∀ (r s b
  t : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∃ m₁ m₂ m₃ : ℕ, r = (m₁ : ℝ) / (M k : ℝ) ∧ s
  = (m₂ : ℝ) / (M k : ℝ) ∧ b = (m₃ : ℝ) / (M k : ℝ)) → ∀ (q a c : ℤ), θ k g {l | (l,t) ∈ E k g ∧ (⌊scalarY l t
  / (D.N k ^ (-r))⌋ : ℤ) = q ∧ (⌊scalarX l t / (D.N k ^ (-s))⌋ : ℤ) = a ∧ l.2 1 ∈ D.vel k b c} ≤
  ENNReal.ofReal (H k * D.N k ^ (-r - D.d * s)) * D.π k g (D.vel k b c)))

/-- Use the same preparation mesh in every consequence of a fixed preparation
certificate. -/
noncomputable def prepMesh {H : ℕ → ℝ}
    {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E) : ℕ → ℕ :=
  Classical.choose hprep.2

def graphData (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence)
    (L : ℝ) (H : ℕ → ℝ) (B : ℝ)
    (G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence) : Prop :=
  Subpower D.N H ∧ L + 10 ≤ B ∧ (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin
  (D.W k), ENNReal.ofReal (D.ω k g) * (D.ρ k g).restrict (E k g) Set.univ ∧ ∀ g : Fin (D.W k), MeasurableSet
  (E k g) ∧ E k g ⊆ E₀ k g ∧ (∀ p ∈ E k g, (∀ e : Fin 2, |G k g (D.phys k B p) e| ≤ H k) ∧ |p.1.2 3 + 2 * p.2
  * p.1.2 4 - G k g (D.phys k B p) 0 - G k g (D.phys k B p) 1 * p.1.2 1| ≤ H k * D.N k ^ (-L)) ∧ (∀ r : ℝ, R⁻¹
  ≤ r → r ≤ R → r ≤ L → ∀ q : Fin 3 → ℤ, ({v : Fin 2 → ℤ | (D.ρ k g).restrict (E k g) {p | D.phys k r p = q
  ∧ D.rowbin k r (G k g (D.phys k B p)) = v} ≠ 0}.ncard : ℝ) ≤ H k) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin
  3 → ℤ) (c : ℤ), (D.ρ k g).restrict (E k g) {p | D.phys k B p = q ∧ p.1.2 1 ∈ D.vel k r c} ≤ ENNReal.ofReal
  (H k) * (D.ρ k g).restrict (E k g) {p | D.phys k B p = q} * D.π k g (D.vel k r c)))

/-- The exact original graph and depth-one packet data used by qualification. -/
def toQualificationTable (B : ℝ)
    (G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
    (E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence) : QualificationTable ScalarLine where
  W := D.W
  n := fun k => D.n k 1
  N := D.N
  h := fun k => ((2 : ℝ) ^ D.T k 1)⁻¹
  ω := D.ω
  ρ := D.ρ
  E := E
  γ := fun k => D.γ k 1
  A := fun k => D.A k 1
  I := fun k i => timeBlock (D.T k 1) (D.j k 1 i)
  row := fun k g p => G k g (D.phys k B p)

def graphOracle (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence) : Prop :=
  ∀ L : ℝ, 0 < L → ∃ H B G E, D.graphData E₀ L H B G E

def qualOracle (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence) : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ L : ℝ, 0 < L → ∃ H B G E,
    D.graphData E₀ L H B G E ∧ ∀ ε : ℝ, 0 < ε →
      Tendsto ((D.toQualificationTable B G E).realFailureRatio M ε) atTop (nhds 0)

/-- A graph may be chosen at a stronger precision than the one requested in
the frozen conclusion. Discovery refers to that same fixed graph. -/
def polynomialDiscovery (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence) : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ L : ℝ, 0 < L → ∃ L' : ℝ, L ≤ L' ∧ 0 < L' ∧
    ∀ (H : ℕ → ℝ) (B : ℝ)
      (G : (k : ℕ) → Fin (D.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ)
      (E : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence),
      D.graphData E₀ L' H B G E → (D.toQualificationTable B G E).SlackDiscovery M

end ScalarData

/-- The analytic discovery assertion left after the exact endpoint assembly.
All assumptions here are literal assumptions of the frozen obligation. -/
def PolynomialDiscoveryStatement : Prop :=
  (∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ C : ℝ, 0 < C ∧
    Submission.Lib.K4ContinuousKakeya.FiniteMK n C) →
  ∀ D : ScalarData, D.Parameters → D.base → D.caps → D.packets →
    ∀ (H₀ : ℕ → ℝ) (θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine)
      (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence),
      D.prepData H₀ θ E₀ → D.polynomialDiscovery E₀

end
end Submission.Obl.k4_scalar_graph_residual_discovery
