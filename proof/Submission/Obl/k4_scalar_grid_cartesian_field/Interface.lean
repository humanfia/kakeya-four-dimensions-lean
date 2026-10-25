import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_scalar_grid_cartesian_field

set_option linter.unusedVariables false

open MeasureTheory Set Filter

/-- The unchanged sequence, world, and packet arrays in the frozen o230 statement. -/
structure Data where
  N : ℕ → ℝ
  K : ℕ → ℝ
  d : ℝ
  κ : ℝ
  S : ℝ
  W : ℕ → ℕ
  ω : (k : ℕ) → Fin (W k) → ℝ
  ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ))
  ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)
  π : (k : ℕ) → Fin (W k) → Measure ℝ
  T : ℕ → ℝ → ℕ
  n : ℕ → ℝ → ℕ
  γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)
  j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)
  A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ))
  u : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ
  v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ
  F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ

noncomputable def y (data : Data) : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ :=
  fun l t => l.2 0 + t * l.2 1

noncomputable def x (data : Data) : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ :=
  fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

noncomputable def I (data : Data) : (T : ℕ) → Fin (2 ^ T) → Set ℝ :=
  fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

noncomputable def z (data : Data) : ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 2 → ℤ :=
  fun B r p e => (⌊(![p.2, (y data) p.1 p.2] : Fin 2 → ℝ) e / (B ^ (-r))⌋ : ℤ)

noncomputable def phys (data : Data) : ℕ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 3 → ℤ :=
  fun k r p e => (⌊(![p.2, (y data) p.1 p.2, (x data) p.1 p.2] : Fin 3 → ℝ) e / (data.N k ^ (-r))⌋ : ℤ)

noncomputable def coeff (data : Data) : ℕ → ℝ → (ℕ × (Fin 5 → ℝ)) → Fin 5 → ℤ :=
  fun k r l e => (⌊l.2 e / (data.N k ^ (-r))⌋ : ℤ)

noncomputable def vel (data : Data) : ℕ → ℝ → ℤ → Set ℝ :=
  fun k r c => {v : ℝ | (⌊v / (data.N k ^ (-r))⌋ : ℤ) = c}

noncomputable def rowbin (data : Data) : ℕ → ℝ → (Fin 2 → ℝ) → Fin 2 → ℤ :=
  fun k r v e => (⌊v e / (data.N k ^ (-r))⌋ : ℤ)

noncomputable def subpower (data : Data) : (ℕ → ℝ) → Prop :=
  fun H => (∀ k, 1 ≤ H k) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ data.N k ^ ε

noncomputable def prepData (data : Data) : (ℕ → ℝ) → ((k : ℕ) → Fin (data.W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) → ((k : ℕ) → Fin (data.W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop :=
  fun H θ E => (subpower data) H ∧
    ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧
    data.N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧
    (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * (data.ρ k g).restrict (E k g) Set.univ ∧
    ∀ g : Fin (data.W k), θ k g ≤ data.ν k g ∧
    θ k g Set.univ ≤ 1 ∧
    MeasurableSet (E k g) ∧
    (∀ p ∈ E k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ e, |p.1.2 e| ≤ H k) ∧
    (∀ᵐ l ∂θ k g, ∀ e, |l.2 e| ≤ H k) ∧
    ENNReal.ofReal ((H k)⁻¹) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ≤ (data.ρ k g).restrict (E k g) ∧
    (data.ρ k g).restrict (E k g) ≤ ENNReal.ofReal (H k) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ∧
    (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) → Set.Finite {q : Fin 3 → ℤ | (data.ρ k g).restrict (E k g) {p | (phys data) k r p = q} ≠ 0} ∧
    ({q : Fin 3 → ℤ | (data.ρ k g).restrict (E k g) {p | (phys data) k r p = q} ≠ 0}.ncard : ℝ) ≤ H k * data.N k ^ ((2 + data.d) * r) ∧
    (∀ r₀ : ℝ, R⁻¹ ≤ r₀ → r₀ ≤ r → (∃ m : ℕ, r₀ = (m : ℝ) / (M k : ℝ)) → ∀ q₀ : Fin 3 → ℤ, ({q : Fin 3 → ℤ | (data.ρ k g).restrict (E k g) {p | (phys data) k r p = q ∧
    (phys data) k r₀ p = q₀} ≠ 0}.ncard : ℝ) ≤ H k * data.N k ^ ((2 + data.d) * (r - r₀))) ∧
    (∀ q : Fin 5 → ℤ, (data.ρ k g).restrict (E k g) {p | (coeff data) k r p.1 = q} ≠ 0 → ENNReal.ofReal (data.N k ^ (-(1 + data.d) * r) / H k) * data.π k g ((vel data) k r (q 1)) ≤ θ k g {l | (coeff data) k r l = q} ∧
    θ k g {l | (coeff data) k r l = q} ≤ ENNReal.ofReal (H k * data.N k ^ (-(1 + data.d) * r)) * data.π k g ((vel data) k r (q 1))) ∧
    (∀ (q : Fin 3 → ℤ) (c : ℤ), ({b : Fin 5 → ℤ | (data.ρ k g).restrict (E k g) {p | (phys data) k r p = q ∧
    (coeff data) k r p.1 1 = c ∧
    (coeff data) k r p.1 = b} ≠ 0}.ncard : ℝ) ≤ H k)) ∧
    (∀ (r s b t : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∃ m₁ m₂ m₃ : ℕ, r = (m₁ : ℝ) / (M k : ℝ) ∧
    s = (m₂ : ℝ) / (M k : ℝ) ∧
    b = (m₃ : ℝ) / (M k : ℝ)) → ∀ (q a c : ℤ), θ k g {l | (l,t) ∈ E k g ∧
    (⌊(y data) l t / (data.N k ^ (-r))⌋ : ℤ) = q ∧
    (⌊(x data) l t / (data.N k ^ (-s))⌋ : ℤ) = a ∧
    l.2 1 ∈ (vel data) k b c} ≤ ENNReal.ofReal (H k * data.N k ^ (-r - data.d * s)) * data.π k g ((vel data) k b c)))

noncomputable def graphData (data : Data) : ((k : ℕ) → Fin (data.W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → ℝ → (ℕ → ℝ) → ℝ → ((k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) → ((k : ℕ) → Fin (data.W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop :=
  fun E₀ L H B G E => (subpower data) H ∧
    L + 10 ≤ B ∧
    (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * (data.ρ k g).restrict (E k g) Set.univ ∧
    ∀ g : Fin (data.W k), MeasurableSet (E k g) ∧
    E k g ⊆ E₀ k g ∧
    (∀ p ∈ E k g, (∀ e : Fin 2, |G k g ((phys data) k B p) e| ≤ H k) ∧
    |p.1.2 3 + 2 * p.2 * p.1.2 4 - G k g ((phys data) k B p) 0 - G k g ((phys data) k B p) 1 * p.1.2 1| ≤ H k * data.N k ^ (-L)) ∧
    (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → r ≤ L → ∀ q : Fin 3 → ℤ, ({v : Fin 2 → ℤ | (data.ρ k g).restrict (E k g) {p | (phys data) k r p = q ∧
    (rowbin data) k r (G k g ((phys data) k B p)) = v} ≠ 0}.ncard : ℝ) ≤ H k) ∧
    (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin 3 → ℤ) (c : ℤ), (data.ρ k g).restrict (E k g) {p | (phys data) k B p = q ∧
    p.1.2 1 ∈ (vel data) k r c} ≤ ENNReal.ofReal (H k) * (data.ρ k g).restrict (E k g) {p | (phys data) k B p = q} * data.π k g ((vel data) k r c)))

noncomputable def graphOracle (data : Data) : ((k : ℕ) → Fin (data.W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop :=
  fun E₀ => ∀ L : ℝ, 0 < L → ∃ (H : ℕ → ℝ) (B : ℝ) (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) (E : (k : ℕ) → Fin (data.W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), (graphData data) E₀ L H B G E

noncomputable def fit (data : Data) : (k : ℕ) → ℕ → ((k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) → ((k : ℕ) → Fin (data.W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin (data.n k 1) → Prop :=
  fun k M G E B ε p i => ∃ P : Fin 2 → Polynomial ℝ, (∀ e, (P e).natDegree ≤ M ∧
    ∀ a : ℕ, |(P e).coeff a| ≤ data.N k ^ ε) ∧
    (∀ e, |G k (data.γ k 1 i) ((phys data) k B p) e - (P e).eval p.2| ≤ ((2 : ℝ) ^ data.T k 1)⁻¹ ^ M) ∧
    ENNReal.ofReal (((2 : ℝ) ^ data.T k 1)⁻¹ * data.N k ^ (-ε)) ≤ MeasureTheory.volume {t : ℝ | (p.1,t) ∈ E k (data.γ k 1 i) ∧
    t ∈ (I data) (data.T k 1) (data.j k 1 i) ∧
    ∀ e, |G k (data.γ k 1 i) ((phys data) k B (p.1,t)) e - (P e).eval t| ≤ ((2 : ℝ) ^ data.T k 1)⁻¹ ^ M}

noncomputable def qualOracle (data : Data) : ((k : ℕ) → Fin (data.W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop :=
  fun E₀ => ∀ M : ℕ, 2 ≤ M → ∀ L : ℝ, 0 < L → ∃ (H : ℕ → ℝ) (B : ℝ) (G : (k : ℕ) → Fin (data.W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) (E : (k : ℕ) → Fin (data.W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), (graphData data) E₀ L H B G E ∧
    ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun k => (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * (data.ρ k g).restrict (E k g) {p | ∃ i : Fin (data.n k 1), data.γ k 1 i = g ∧
    p.1 ∈ data.A k 1 i ∧
    p.2 ∈ (I data) (data.T k 1) (data.j k 1 i) ∧
    ¬ (fit data) k M G E B ε p i}).toReal / (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) * (data.ρ k g).restrict (E k g) Set.univ).toReal) Filter.atTop (nhds (0 : ℝ))

noncomputable def fieldStatement (data : Data) : Prop :=
  ∃ (H : ℕ → ℝ) (D : ℕ) (Z B : ℝ), (subpower data) H ∧
    10 ≤ Z ∧
    Z + 10 ≤ B ∧
    ∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∃ (i : Fin (data.n k 1)) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z₀ : Fin 2 → ℝ) (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ), (fun (h : ℝ) => MeasurableSet (data.A k 1 i) ∧
    MeasureTheory.IsProbabilityMeasure (data.ν k (data.γ k 1 i)) ∧
    MeasureTheory.IsProbabilityMeasure (data.π k (data.γ k 1 i)) ∧
    (∀ᵐ l ∂data.ν k (data.γ k 1 i), ∀ e, |l.2 e| ≤ H k) ∧
    data.N k ^ (-data.κ) / H k ≤ h ∧
    h ≤ H k * data.N k ^ (-data.κ) ∧
    0 < h ∧
    h ≤ 1 ∧
    ENNReal.ofReal (data.N k ^ (-data.d) * h / H k) ≤ data.ν k (data.γ k 1 i) (data.A k 1 i) ∧
    data.ν k (data.γ k 1 i) (data.A k 1 i) ≤ ENNReal.ofReal (H k * data.N k ^ (-data.d) * h) ∧
    μ ≤ data.ρ k (data.γ k 1 i) ∧
    μ ≤ ENNReal.ofReal (H k) • ((data.ν k (data.γ k 1 i)).prod MeasureTheory.volume) ∧
    μ {p | p.1 ∈ data.A k 1 i ∧
    p.2 ∈ (I data) (data.T k 1) (data.j k 1 i)}ᶜ = 0 ∧
    ENNReal.ofReal (h / H k) * data.ν k (data.γ k 1 i) (data.A k 1 i) ≤ μ Set.univ ∧
    z₀ 0 = (((data.j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ data.T k 1) ∧
    (∀ e, |z₀ e| ≤ H k) ∧
    (∀ᵐ p ∂μ, ∀ t ∈ (I data) (data.T k 1) (data.j k 1 i), ∀ e : Fin 2, |(![t, (y data) p.1 t] e - z₀ e) / h| ≤ H k) ∧
    (∀ q : Fin 2 → ℤ, μ {p | (fun e : Fin 2 => (⌊((![p.2,(y data) p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (data.N k ^ (-Z))⌋ : ℤ)) = q} ≤ ENNReal.ofReal ((H k * h) * data.N k ^ (-2 * Z)) * data.ν k (data.γ k 1 i) (data.A k 1 i)) ∧
    (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → (∀ c : ℤ, data.π k (data.γ k 1 i) ((vel data) k r c) ≤ ENNReal.ofReal (H k * data.N k ^ (-data.S * r))) ∧
    ∀ (q : Fin 3 → ℤ) (c : ℤ), μ {p | (phys data) k B p = q ∧
    p.1.2 1 ∈ (vel data) k r c} ≤ ENNReal.ofReal (H k) * μ {p | (phys data) k B p = q} * data.π k (data.γ k 1 i) ((vel data) k r c)) ∧
    (∀ e, (𝒯 e).totalDegree ≤ D ∧
    ∀ b, |(𝒯 e).coeff b| ≤ H k) ∧
    (∀ᵐ p ∂μ, ∀ t ∈ (I data) (data.T k 1) (data.j k 1 i), |p.1.2 3 + 2 * t * p.1.2 4 - ∑ e : Fin 2, MvPolynomial.eval (fun e : Fin 2 => ((![t,(y data) p.1 t] : Fin 2 → ℝ) e - z₀ e) / h) (𝒯 e) * (![1,p.1.2 1] : Fin 2 → ℝ) e| ≤ H k * data.N k ^ (-1 : ℝ) * h ^ (-(3 : ℝ)/4)) ∧
    (∀ w : ℝ, data.N k ^ (-1 : ℝ) * h ^ ((1 : ℝ)/8) ≤ w → w ≤ data.N k ^ (-1 : ℝ) → Set.Finite {q : (Fin 2 → ℤ) × ℤ | μ {p | (fun e : Fin 2 => (⌊((![p.2,(y data) p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (data.N k ^ (-Z))⌋ : ℤ)) = q.1 ∧
    (⌊(x data) p.1 p.2 / w⌋ : ℤ) = q.2} ≠ 0} ∧
    ({q : (Fin 2 → ℤ) × ℤ | μ {p | (fun e : Fin 2 => (⌊((![p.2,(y data) p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (data.N k ^ (-Z))⌋ : ℤ)) = q.1 ∧
    (⌊(x data) p.1 p.2 / w⌋ : ℤ) = q.2} ≠ 0}.ncard : ℝ) ≤ H k * data.N k ^ (2 * Z) * (data.N k ^ (-1 : ℝ) / w) ^ data.d)) (((2 : ℝ) ^ data.T k 1)⁻¹)

noncomputable def baseHyp (data : Data) : Prop :=
  (∀ k, (∀ g, 0 ≤ data.ω k g) ∧
    (∑ g, data.ω k g) = 1 ∧
    (∀ g, MeasureTheory.IsProbabilityMeasure (data.ν k g) ∧
    MeasureTheory.IsProbabilityMeasure (data.π k g) ∧
    (∀ᵐ l ∂data.ν k g, ∀ e, |l.2 e| ≤ data.K k) ∧
    data.ρ k g ≤ ENNReal.ofReal (data.K k) • ((data.ν k g).prod MeasureTheory.volume) ∧
    data.ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧
    ENNReal.ofReal ((data.K k)⁻¹) ≤ ∑ g, ENNReal.ofReal (data.ω k g) * data.ρ k g Set.univ)

noncomputable def capHyp (data : Data) : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (data.W k)) (r s b : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∀ c : ℤ, data.π k g {v : ℝ | (⌊v / (data.N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (data.K k * data.N k ^ (-data.S * b))) ∧
    (∀ (q : Fin 2 → ℤ) (a : ℤ), data.ρ k g {p | (z data) (data.N k) r p = q ∧
    (⌊(x data) p.1 p.2 / (data.N k ^ (-s))⌋ : ℤ) = a} ≤ ENNReal.ofReal (data.K k * data.N k ^ (-2 * r - data.d * s))) ∧
    (∀ (q : Fin 2 → ℤ) (a c : ℤ), data.ρ k g {p | (z data) (data.N k) r p = q ∧
    (⌊(x data) p.1 p.2 / (data.N k ^ (-s))⌋ : ℤ) = a ∧
    (⌊p.1.2 1 / (data.N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (data.K k * data.N k ^ (-2 * r - data.d * s)) * data.π k g {v : ℝ | (⌊v / (data.N k ^ (-b))⌋ : ℤ) = c}))

noncomputable def packetHyp (data : Data) : Prop :=
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → data.N k ^ (data.κ * s) / data.K k ≤ (2 : ℝ) ^ data.T k s ∧
    (2 : ℝ) ^ data.T k s ≤ data.K k * data.N k ^ (data.κ * s) ∧
    (∀ i, MeasurableSet (data.A k s i)) ∧
    (∀ i i', i ≠ i' → data.γ k s i = data.γ k s i' → data.j k s i = data.j k s i' → Disjoint (data.A k s i) (data.A k s i')) ∧
    (∀ i, ENNReal.ofReal (data.N k ^ (-data.d * s) / (data.K k * (2 : ℝ) ^ data.T k s)) ≤ data.ν k (data.γ k s i) (data.A k s i) ∧
    data.ν k (data.γ k s i) (data.A k s i) ≤ ENNReal.ofReal (data.K k * data.N k ^ (-data.d * s) / (2 : ℝ) ^ data.T k s) ∧
    ENNReal.ofReal ((data.K k * (2 : ℝ) ^ data.T k s)⁻¹) * data.ν k (data.γ k s i) (data.A k s i) ≤ data.ρ k (data.γ k s i) (data.A k s i ×ˢ (I data) (data.T k s) (data.j k s i)) ∧
    |data.u k s i| + |data.v k s i| ≤ data.K k ∧
    (data.F k s i).totalDegree ≤ 2 ∧
    (∀ t ∈ (I data) (data.T k s) (data.j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2, |MvPolynomial.eval ![t, data.u k s i + t * data.v k s i + w / (2 : ℝ) ^ data.T k s] (data.F k s i)| ≤ data.K k) ∧
    (∀ l ∈ data.A k s i, ∀ t ∈ (I data) (data.T k s) (data.j k s i), |(y data) l t - data.u k s i - t * data.v k s i| ≤ data.K k / (2 : ℝ) ^ data.T k s ∧
    |(x data) l t - MvPolynomial.eval ![t, (y data) l t] (data.F k s i)| ≤ data.K k * data.N k ^ (-s))) ∧
    (∀ g : Fin (data.W k), data.ρ k g {p | ∃ i, data.γ k s i = g ∧
    p.1 ∈ data.A k s i ∧
    p.2 ∈ (I data) (data.T k s) (data.j k s i)}ᶜ = 0))

noncomputable def FieldTheorem (data : Data) : Prop :=
  baseHyp data → capHyp data → packetHyp data →
  ∀ (H₀ : ℕ → ℝ) (θ : (k : ℕ) → Fin (data.W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E₀ : (k : ℕ) → Fin (data.W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), (prepData data) H₀ θ E₀ → (qualOracle data) E₀ → (fieldStatement data)

noncomputable def scaleHyp (data : Data) : Prop :=
  (∀ k, 2 ≤ data.N k) ∧ Tendsto data.N atTop atTop ∧ subpower data data.K ∧
  0 ≤ data.d ∧ data.d < 1 ∧ 0 < data.κ ∧ data.κ ≤ 1 ∧ 0 < data.S

noncomputable def MultilinearKakeya : Prop :=
  (∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) → (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → MeasureTheory.lintegral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * (Metric.thickening r (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) x)) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤ ENNReal.ofReal (C * r ^ n * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1))))

/-- This named interface elaborates to the frozen statement without changing any hypothesis. -/
theorem of_field_theorem
    (hcore : MultilinearKakeya → ∀ data : Data, scaleHyp data → FieldTheorem data) :
    (∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) → (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → MeasureTheory.lintegral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * (Metric.thickening r (Set.range fun t : ℝ => a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) x)) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) ≤ ENNReal.ofReal (C * r ^ n * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1)))) → ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) → ∀ d κ S : ℝ, 0 ≤ d → d < 1 → 0 < κ → κ ≤ 1 → 0 < S → ∀ (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ) (T n : ℕ → ℝ → ℕ) (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k)) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)) (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ))) (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ) (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ), (fun (y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => (fun (x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => (fun (I : (T : ℕ) → Fin (2 ^ T) → Set ℝ) => (fun (z : ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 2 → ℤ) => (fun (phys : ℕ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin 3 → ℤ) => (fun (coeff : ℕ → ℝ → (ℕ × (Fin 5 → ℝ)) → Fin 5 → ℤ) => (fun (vel : ℕ → ℝ → ℤ → Set ℝ) => (fun (rowbin : ℕ → ℝ → (Fin 2 → ℝ) → Fin 2 → ℤ) => (fun (subpower : (ℕ → ℝ) → Prop) => (fun (prepData : (ℕ → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) => (fun (graphData : ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → ℝ → (ℕ → ℝ) → ℝ → ((k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) => (fun (graphOracle : ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) => (fun (fit : (k : ℕ) → ℕ → ((k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → ℝ → ℝ → ((ℕ × (Fin 5 → ℝ)) × ℝ) → Fin (n k 1) → Prop) => (fun (qualOracle : ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) → Prop) => (fun (field : Prop) => (∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1 ∧ (∀ g, MeasureTheory.IsProbabilityMeasure (ν k g) ∧ MeasureTheory.IsProbabilityMeasure (π k g) ∧ (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧ ρ k g ≤ ENNReal.ofReal (K k) • ((ν k g).prod MeasureTheory.volume) ∧ ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (W k)) (r s b : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∀ c : ℤ, π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-S * b))) ∧ (∀ (q : Fin 2 → ℤ) (a : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s))) ∧ (∀ (q : Fin 2 → ℤ) (a c : ℤ), ρ k g {p | z (N k) r p = q ∧ (⌊x p.1 p.2 / (N k ^ (-s))⌋ : ℤ) = a ∧ (⌊p.1.2 1 / (N k ^ (-b))⌋ : ℤ) = c} ≤ ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) * π k g {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = c})) → (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧ (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧ (∀ i, MeasurableSet (A k s i)) ∧ (∀ i i', i ≠ i' → γ k s i = γ k s i' → j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧ (∀ i, ENNReal.ofReal (N k ^ (-d * s) / (K k * (2 : ℝ) ^ T k s)) ≤ ν k (γ k s i) (A k s i) ∧ ν k (γ k s i) (A k s i) ≤ ENNReal.ofReal (K k * N k ^ (-d * s) / (2 : ℝ) ^ T k s) ∧ ENNReal.ofReal ((K k * (2 : ℝ) ^ T k s)⁻¹) * ν k (γ k s i) (A k s i) ≤ ρ k (γ k s i) (A k s i ×ˢ I (T k s) (j k s i)) ∧ |u k s i| + |v k s i| ≤ K k ∧ (F k s i).totalDegree ≤ 2 ∧ (∀ t ∈ I (T k s) (j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2, |MvPolynomial.eval ![t, u k s i + t * v k s i + w / (2 : ℝ) ^ T k s] (F k s i)| ≤ K k) ∧ (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i), |y l t - u k s i - t * v k s i| ≤ K k / (2 : ℝ) ^ T k s ∧ |x l t - MvPolynomial.eval ![t, y l t] (F k s i)| ≤ K k * N k ^ (-s))) ∧ (∀ g : Fin (W k), ρ k g {p | ∃ i, γ k s i = g ∧ p.1 ∈ A k s i ∧ p.2 ∈ I (T k s) (j k s i)}ᶜ = 0)) → ∀ (H₀ : ℕ → ℝ) (θ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E₀ : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), prepData H₀ θ E₀ → qualOracle E₀ → field) (∃ (H : ℕ → ℝ) (D : ℕ) (Z B : ℝ), subpower H ∧ 10 ≤ Z ∧ Z + 10 ≤ B ∧ ∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∃ (i : Fin (n k 1)) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z₀ : Fin 2 → ℝ) (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ), (fun (h : ℝ) => MeasurableSet (A k 1 i) ∧ MeasureTheory.IsProbabilityMeasure (ν k (γ k 1 i)) ∧ MeasureTheory.IsProbabilityMeasure (π k (γ k 1 i)) ∧ (∀ᵐ l ∂ν k (γ k 1 i), ∀ e, |l.2 e| ≤ H k) ∧ N k ^ (-κ) / H k ≤ h ∧ h ≤ H k * N k ^ (-κ) ∧ 0 < h ∧ h ≤ 1 ∧ ENNReal.ofReal (N k ^ (-d) * h / H k) ≤ ν k (γ k 1 i) (A k 1 i) ∧ ν k (γ k 1 i) (A k 1 i) ≤ ENNReal.ofReal (H k * N k ^ (-d) * h) ∧ μ ≤ ρ k (γ k 1 i) ∧ μ ≤ ENNReal.ofReal (H k) • ((ν k (γ k 1 i)).prod MeasureTheory.volume) ∧ μ {p | p.1 ∈ A k 1 i ∧ p.2 ∈ I (T k 1) (j k 1 i)}ᶜ = 0 ∧ ENNReal.ofReal (h / H k) * ν k (γ k 1 i) (A k 1 i) ≤ μ Set.univ ∧ z₀ 0 = (((j k 1 i : ℕ) : ℝ) / (2 : ℝ) ^ T k 1) ∧ (∀ e, |z₀ e| ≤ H k) ∧ (∀ᵐ p ∂μ, ∀ t ∈ I (T k 1) (j k 1 i), ∀ e : Fin 2, |(![t, y p.1 t] e - z₀ e) / h| ≤ H k) ∧ (∀ q : Fin 2 → ℤ, μ {p | (fun e : Fin 2 => (⌊((![p.2,y p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (N k ^ (-Z))⌋ : ℤ)) = q} ≤ ENNReal.ofReal ((H k * h) * N k ^ (-2 * Z)) * ν k (γ k 1 i) (A k 1 i)) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → (∀ c : ℤ, π k (γ k 1 i) (vel k r c) ≤ ENNReal.ofReal (H k * N k ^ (-S * r))) ∧ ∀ (q : Fin 3 → ℤ) (c : ℤ), μ {p | phys k B p = q ∧ p.1.2 1 ∈ vel k r c} ≤ ENNReal.ofReal (H k) * μ {p | phys k B p = q} * π k (γ k 1 i) (vel k r c)) ∧ (∀ e, (𝒯 e).totalDegree ≤ D ∧ ∀ b, |(𝒯 e).coeff b| ≤ H k) ∧ (∀ᵐ p ∂μ, ∀ t ∈ I (T k 1) (j k 1 i), |p.1.2 3 + 2 * t * p.1.2 4 - ∑ e : Fin 2, MvPolynomial.eval (fun e : Fin 2 => ((![t,y p.1 t] : Fin 2 → ℝ) e - z₀ e) / h) (𝒯 e) * (![1,p.1.2 1] : Fin 2 → ℝ) e| ≤ H k * N k ^ (-1 : ℝ) * h ^ (-(3 : ℝ)/4)) ∧ (∀ w : ℝ, N k ^ (-1 : ℝ) * h ^ ((1 : ℝ)/8) ≤ w → w ≤ N k ^ (-1 : ℝ) → Set.Finite {q : (Fin 2 → ℤ) × ℤ | μ {p | (fun e : Fin 2 => (⌊((![p.2,y p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (N k ^ (-Z))⌋ : ℤ)) = q.1 ∧ (⌊x p.1 p.2 / w⌋ : ℤ) = q.2} ≠ 0} ∧ ({q : (Fin 2 → ℤ) × ℤ | μ {p | (fun e : Fin 2 => (⌊((![p.2,y p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h / (N k ^ (-Z))⌋ : ℤ)) = q.1 ∧ (⌊x p.1 p.2 / w⌋ : ℤ) = q.2} ≠ 0}.ncard : ℝ) ≤ H k * N k ^ (2 * Z) * (N k ^ (-1 : ℝ) / w) ^ d)) (((2 : ℝ) ^ T k 1)⁻¹))) (fun E₀ => ∀ M : ℕ, 2 ≤ M → ∀ L : ℝ, 0 < L → ∃ (H : ℕ → ℝ) (B : ℝ) (G : (k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), graphData E₀ L H B G E ∧ ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun k => (∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) {p | ∃ i : Fin (n k 1), γ k 1 i = g ∧ p.1 ∈ A k 1 i ∧ p.2 ∈ I (T k 1) (j k 1 i) ∧ ¬ fit k M G E B ε p i}).toReal / (∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ).toReal) Filter.atTop (nhds (0 : ℝ)))) (fun k M G E B ε p i => ∃ P : Fin 2 → Polynomial ℝ, (∀ e, (P e).natDegree ≤ M ∧ ∀ a : ℕ, |(P e).coeff a| ≤ N k ^ ε) ∧ (∀ e, |G k (γ k 1 i) (phys k B p) e - (P e).eval p.2| ≤ ((2 : ℝ) ^ T k 1)⁻¹ ^ M) ∧ ENNReal.ofReal (((2 : ℝ) ^ T k 1)⁻¹ * N k ^ (-ε)) ≤ MeasureTheory.volume {t : ℝ | (p.1,t) ∈ E k (γ k 1 i) ∧ t ∈ I (T k 1) (j k 1 i) ∧ ∀ e, |G k (γ k 1 i) (phys k B (p.1,t)) e - (P e).eval t| ≤ ((2 : ℝ) ^ T k 1)⁻¹ ^ M})) (fun E₀ => ∀ L : ℝ, 0 < L → ∃ (H : ℕ → ℝ) (B : ℝ) (G : (k : ℕ) → Fin (W k) → (Fin 3 → ℤ) → Fin 2 → ℝ) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), graphData E₀ L H B G E)) (fun E₀ L H B G E => subpower H ∧ L + 10 ≤ B ∧ (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ ∧ ∀ g : Fin (W k), MeasurableSet (E k g) ∧ E k g ⊆ E₀ k g ∧ (∀ p ∈ E k g, (∀ e : Fin 2, |G k g (phys k B p) e| ≤ H k) ∧ |p.1.2 3 + 2 * p.2 * p.1.2 4 - G k g (phys k B p) 0 - G k g (phys k B p) 1 * p.1.2 1| ≤ H k * N k ^ (-L)) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → r ≤ L → ∀ q : Fin 3 → ℤ, ({v : Fin 2 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q ∧ rowbin k r (G k g (phys k B p)) = v} ≠ 0}.ncard : ℝ) ≤ H k) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin 3 → ℤ) (c : ℤ), (ρ k g).restrict (E k g) {p | phys k B p = q ∧ p.1.2 1 ∈ vel k r c} ≤ ENNReal.ofReal (H k) * (ρ k g).restrict (E k g) {p | phys k B p = q} * π k g (vel k r c))))) (fun H θ E => subpower H ∧ ∃ M : ℕ → ℕ, (∀ k, 1 ≤ M k ∧ N k ^ ((1 : ℝ) / (M k : ℝ)) ≤ H k) ∧ (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ENNReal.ofReal ((H k)⁻¹) ≤ ∑ g : Fin (W k), ENNReal.ofReal (ω k g) * (ρ k g).restrict (E k g) Set.univ ∧ ∀ g : Fin (W k), θ k g ≤ ν k g ∧ θ k g Set.univ ≤ 1 ∧ MeasurableSet (E k g) ∧ (∀ p ∈ E k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H k) ∧ (∀ᵐ l ∂θ k g, ∀ e, |l.2 e| ≤ H k) ∧ ENNReal.ofReal ((H k)⁻¹) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ≤ (ρ k g).restrict (E k g) ∧ (ρ k g).restrict (E k g) ≤ ENNReal.ofReal (H k) • (((θ k g).prod MeasureTheory.volume).restrict (E k g)) ∧ (∀ r : ℝ, R⁻¹ ≤ r → r ≤ R → (∃ m : ℕ, r = (m : ℝ) / (M k : ℝ)) → Set.Finite {q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q} ≠ 0} ∧ ({q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q} ≠ 0}.ncard : ℝ) ≤ H k * N k ^ ((2 + d) * r) ∧ (∀ r₀ : ℝ, R⁻¹ ≤ r₀ → r₀ ≤ r → (∃ m : ℕ, r₀ = (m : ℝ) / (M k : ℝ)) → ∀ q₀ : Fin 3 → ℤ, ({q : Fin 3 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q ∧ phys k r₀ p = q₀} ≠ 0}.ncard : ℝ) ≤ H k * N k ^ ((2 + d) * (r - r₀))) ∧ (∀ q : Fin 5 → ℤ, (ρ k g).restrict (E k g) {p | coeff k r p.1 = q} ≠ 0 → ENNReal.ofReal (N k ^ (-(1 + d) * r) / H k) * π k g (vel k r (q 1)) ≤ θ k g {l | coeff k r l = q} ∧ θ k g {l | coeff k r l = q} ≤ ENNReal.ofReal (H k * N k ^ (-(1 + d) * r)) * π k g (vel k r (q 1))) ∧ (∀ (q : Fin 3 → ℤ) (c : ℤ), ({b : Fin 5 → ℤ | (ρ k g).restrict (E k g) {p | phys k r p = q ∧ coeff k r p.1 1 = c ∧ coeff k r p.1 = b} ≠ 0}.ncard : ℝ) ≤ H k)) ∧ (∀ (r s b t : ℝ), R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R → (∃ m₁ m₂ m₃ : ℕ, r = (m₁ : ℝ) / (M k : ℝ) ∧ s = (m₂ : ℝ) / (M k : ℝ) ∧ b = (m₃ : ℝ) / (M k : ℝ)) → ∀ (q a c : ℤ), θ k g {l | (l,t) ∈ E k g ∧ (⌊y l t / (N k ^ (-r))⌋ : ℤ) = q ∧ (⌊x l t / (N k ^ (-s))⌋ : ℤ) = a ∧ l.2 1 ∈ vel k b c} ≤ ENNReal.ofReal (H k * N k ^ (-r - d * s)) * π k g (vel k b c))))) (fun H => (∀ k, 1 ≤ H k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, H k ≤ N k ^ ε)) (fun k r v e => (⌊v e / (N k ^ (-r))⌋ : ℤ))) (fun k r c => {v : ℝ | (⌊v / (N k ^ (-r))⌋ : ℤ) = c})) (fun k r l e => (⌊l.2 e / (N k ^ (-r))⌋ : ℤ))) (fun k r p e => (⌊(![p.2, y p.1 p.2, x p.1 p.2] : Fin 3 → ℝ) e / (N k ^ (-r))⌋ : ℤ))) (fun B r p e => (⌊(![p.2, y p.1 p.2] : Fin 2 → ℝ) e / (B ^ (-r))⌋ : ℤ))) (fun T j => Set.Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))) (fun l t => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4)) (fun l t => l.2 0 + t * l.2 1) := by
  intro hMK N K hN hNt hK d κ S hd0 hd1 hκ0 hκ1 hS W ω ν ρ π T n γ j A u v F
  let data : Data := ⟨N, K, d, κ, S, W, ω, ν, ρ, π, T, n, γ, j, A, u, v, F⟩
  exact hcore hMK data ⟨hN, hNt, hK, hd0, hd1, hκ0, hκ1, hS⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
