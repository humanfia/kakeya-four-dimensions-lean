import Submission.Obl.k4_scalar_guarded_tangent_obstruction.Tangent
import Submission.Obl.k4_scalar_guarded_tangent_obstruction.Accessors

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_guarded_tangent_obstruction

noncomputable section

/-- A full original-coordinate true layer, including its earlier incidence
witness and the list at the original terminal observation. -/
def Layer (w : ℕ) : Type :=
  Σ T : ℕ, Σ n : ℕ,
    (Fin n → Fin w) × (Fin n → Fin (2 ^ T)) ×
    (Fin n → Set Coeff) × (Fin n → Set Incidence) ×
    (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) ×
    (Fin n → MvPolynomial (Fin 2) ℝ) ×
    (Fin w → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n))

namespace Layer

abbrev T {w : ℕ} (a : Layer w) : ℕ := a.1
abbrev n {w : ℕ} (a : Layer w) : ℕ := a.2.1
abbrev world {w : ℕ} (a : Layer w) : Fin a.n → Fin w := a.2.2.1
abbrev block {w : ℕ} (a : Layer w) : Fin a.n → Fin (2 ^ a.T) := a.2.2.2.1
abbrev assignment {w : ℕ} (a : Layer w) : Fin a.n → Set Coeff := a.2.2.2.2.1
abbrev witness {w : ℕ} (a : Layer w) : Fin a.n → Set Incidence := a.2.2.2.2.2.1
abbrev u {w : ℕ} (a : Layer w) : Fin a.n → ℝ := a.2.2.2.2.2.2.1
abbrev v {w : ℕ} (a : Layer w) : Fin a.n → ℝ := a.2.2.2.2.2.2.2.1
abbrev width {w : ℕ} (a : Layer w) : Fin a.n → ℝ := a.2.2.2.2.2.2.2.2.1
abbrev graph {w : ℕ} (a : Layer w) : Fin a.n → MvPolynomial (Fin 2) ℝ :=
  a.2.2.2.2.2.2.2.2.2.1
abbrev list {w : ℕ} (a : Layer w) :
    Fin w → ((Fin 2 → ℝ) × ℤ) → Finset (Fin a.n) := a.2.2.2.2.2.2.2.2.2.2

end Layer

def TangentInput (N K : ℕ → ℝ) (d κ S : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Coeff)
    (ρ : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Incidence)
    (π : (k : ℕ) → Fin (W k) → MeasureTheory.Measure ℝ)
    (T n : ℕ → ℝ → ℕ)
    (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k))
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set Coeff)
    (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ)
    (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ) : Prop :=
  ((∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧
    ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε) ∧
    0 ≤ d ∧ d < 1 ∧ 0 < κ ∧ κ ≤ 1 ∧ 0 < S ∧
    (∀ k, (∀ g, 0 ≤ ω k g) ∧ (∑ g, ω k g) = 1 ∧
    (∀ g, MeasureTheory.IsProbabilityMeasure (ν k g) ∧ MeasureTheory.IsProbabilityMeasure (π k g) ∧
      (∀ᵐ l ∂ν k g, ∀ e, |l.2 e| ≤ K k) ∧
      ρ k g ≤ ENNReal.ofReal (K k) • ((ν k g).prod MeasureTheory.volume) ∧
      ρ k g (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) ∧
    ENNReal.ofReal ((K k)⁻¹) ≤
      ∑ g, ENNReal.ofReal (ω k g) * ρ k g Set.univ) ∧
    (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ (g : Fin (W k)) (r s b : ℝ),
    R⁻¹ ≤ r → r ≤ R → R⁻¹ ≤ s → s ≤ R → R⁻¹ ≤ b → b ≤ R →
    (∀ c : ℤ, π k g {v | velocityBin (N k) b v = c} ≤
      ENNReal.ofReal (K k * N k ^ (-S * b))) ∧
    (∀ (q : Fin 2 → ℤ) (c : ℤ), ρ k g
      {p | baseBin (N k) r p = q ∧ hiddenBin (N k) s p = c} ≤
      ENNReal.ofReal (K k * N k ^ (-2 * r - d * s))) ∧
    (∀ (q : Fin 2 → ℤ) (c e : ℤ), ρ k g
      {p | baseBin (N k) r p = q ∧ hiddenBin (N k) s p = c ∧
        velocityBin (N k) b (p.1.2 1) = e} ≤
      ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) *
        π k g {v | velocityBin (N k) b v = e})) ∧
    (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R →
    N k ^ (κ * s) / K k ≤ (2 : ℝ) ^ T k s ∧
    (2 : ℝ) ^ T k s ≤ K k * N k ^ (κ * s) ∧
    (∀ i, MeasurableSet (A k s i)) ∧
    (∀ i i', i ≠ i' → γ k s i = γ k s i' →
      j k s i = j k s i' → Disjoint (A k s i) (A k s i')) ∧
    (∀ i, ENNReal.ofReal (N k ^ (-d * s) / (K k * (2 : ℝ) ^ T k s)) ≤
        ν k (γ k s i) (A k s i) ∧
      ν k (γ k s i) (A k s i) ≤
        ENNReal.ofReal (K k * N k ^ (-d * s) / (2 : ℝ) ^ T k s) ∧
      ENNReal.ofReal ((K k * (2 : ℝ) ^ T k s)⁻¹) *
        ν k (γ k s i) (A k s i) ≤
        ρ k (γ k s i) (A k s i ×ˢ I (T k s) (j k s i)) ∧
      |u k s i| + |v k s i| ≤ K k ∧ (F k s i).totalDegree ≤ 2 ∧
      (∀ t ∈ I (T k s) (j k s i), ∀ w ∈ Set.Icc (-2 : ℝ) 2,
        |MvPolynomial.eval ![t, u k s i + t * v k s i + w / (2 : ℝ) ^ T k s]
          (F k s i)| ≤ K k) ∧
      (∀ l ∈ A k s i, ∀ t ∈ I (T k s) (j k s i),
        |y l t - u k s i - t * v k s i| ≤ K k / (2 : ℝ) ^ T k s ∧
        |x l t - MvPolynomial.eval ![t, y l t] (F k s i)| ≤
          K k * N k ^ (-s))) ∧
    (∀ g : Fin (W k), ρ k g
      {p | ∃ i, γ k s i = g ∧ p.1 ∈ A k s i ∧
        p.2 ∈ I (T k s) (j k s i)}ᶜ = 0)))

/-- The intermediate package contains only original exact laws, sampled
finite layers and their measurable restrictions. No candidate-return rule
is an assumption of this package. -/
def GuardedPrepared : Prop :=
  ∃ (p : ℕ → RawData) (sample : ℕ → ℕ)
    (scale H buffer K : ℕ → ℝ) (M count : ℕ → ℕ)
    (node : (k : ℕ) → ℝ → Fin (count k))
    (depth time : (k : ℕ) → Fin (count k) → ℝ)
    (layers : (k : ℕ) → Fin (count k) → Layer ((p k).1 (sample k)))
    (ρ : (k : ℕ) → Fin ((p k).1 (sample k)) → MeasureTheory.Measure Incidence)
    (π : (k : ℕ) → Fin ((p k).1 (sample k)) → MeasureTheory.Measure ℝ)
    (d κ S : ℝ),
  let N₀ : ℕ → ℝ := fun k => (p k).N (sample k)
  let N : ℕ → ℝ := fun k => N₀ k ^ scale k
  let actual : ℕ → ℝ := fun k => (H k * Real.log (N₀ k)) ^ (k + 1)
  let loss : ℕ → ℝ := fun k => Real.log (actual k) / Real.log (N₀ k)
  let guard : ℕ → ℕ := fun k => 2 ^ ((M k + k + 1) ^ 2)
  (∀ k, Exact (p k)) ∧
  (∀ k, 0 < scale k ∧ scale k ≤ 1 ∧ 2 ≤ H k ∧ 0 < buffer k ∧
    1 ≤ M k ∧ (p k).M ≤ M k ∧ (p k).D ≤ M k ∧ (p k).L ≤ (M k : ℝ) ∧
    (p k).K (sample k) ≤ H k ∧ (count k : ℝ) ≤ H k ∧
    H k ≤ N₀ k ^ (M k : ℝ)) ∧
  Filter.Tendsto scale Filter.atTop (nhds 0) ∧
  Filter.Tendsto buffer Filter.atTop (nhds 0) ∧
  (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, actual k ≤ N k ^ ε) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, scale k * R < (p k).L) ∧
  (∀ k g, ρ k g ≤ mu (p k) (sample k) g) ∧
  (∀ k, ENNReal.ofReal ((H k)⁻¹) ≤
    ∑ g, ENNReal.ofReal ((p k).weight (sample k) g) * ρ k g Set.univ) ∧
  (∀ k ℓ, let f := layers k ℓ
    0 ≤ depth k ℓ ∧ scale k * depth k ℓ < (p k).L ∧
    ChartData (p k) (M k) (scale k * depth k ℓ) (p k).L
      (scale k * time k ℓ) (Real.log (H k) / Real.log (N₀ k)) true (sample k)
      f.T f.n f.world f.block f.assignment f.witness f.u f.v f.width f.graph f.list ∧
    (∀ i, (H k * (2 : ℝ) ^ f.T)⁻¹ ≤ f.width i) ∧
    (∀ g, ρ k g {z | ∃ i, f.world i = g ∧ z ∈ f.witness i}ᶜ = 0)) ∧
  TangentInput N K d κ S (fun k => (p k).1 (sample k))
    (fun k => (p k).weight (sample k)) (fun k => (p k).prior (sample k)) ρ π
    (fun k s => (layers k (node k s)).T)
    (fun k s => (layers k (node k s)).n)
    (fun k s => (layers k (node k s)).world)
    (fun k s => (layers k (node k s)).block)
    (fun k s => (layers k (node k s)).assignment)
    (fun k s => (layers k (node k s)).u)
    (fun k s => (layers k (node k s)).v)
    (fun k s => (layers k (node k s)).graph) ∧
  (∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop, ∀ r h : ℝ,
    R⁻¹ ≤ r → r ≤ R → h ≤ κ * r - buffer k →
    ¬Chart (p k) (guard k) (scale k * r) (p k).L (scale k * h)
      (loss k) false (sample k))

end

end Submission.Obl.k4_scalar_guarded_tangent_obstruction
