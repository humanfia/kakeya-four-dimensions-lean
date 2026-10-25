import Submission.Obl.k4_horizontal_strict_parameter_step.RawCharts
import Submission.Obl.k4_horizontal_strict_parameter_step.Interface

/-!
# The join of the comparison half and the chart half of the strict step

`ComparedLayer` is what the comparison half (full-time comparison of the old predictors with
the true affine entries, the time-only rows, and the scalar support count from nested true
labels) hands to the chart half (fixed conditional prior, density and duration preparation,
instantaneous mixed caps, and the assembly of a `RawChartFamily`).

At one sample `k` it consists of one old full-time layer `G(u)` at depth `s₀`
(`D = N^(-u s₀)`, `a = N^(-s₀)`, current law `ρH ≤ ρ`), a dense current law `σ ≤ ρH`, and in
every old label `A i` a measurable time-only row `F i` and a measurable labeled event `E i`
inside `A i ×ˢ [0,1]`, `σ`-conull there, on which the normalized scalar of the chart has the
support count down to the floor `ζ`. The old labels `A i` stay whole: they carry the fixed
conditional priors. All restrictions are in the events `E i`.

`ComparedStep` asks for such layers at every depth and every loss, for every prepared input;
`rawStepPreparation_of_compared` (in `ChartAssembly.lean`) turns it into
`RawStepPreparation`.
-/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter

noncomputable section

/-- One old layer with comparison rows and support-counted labeled events, at one sample. -/
structure ComparedLayer (N : ℕ → ℝ) (d e₀ : ℝ) {α : Type} [MeasurableSpace α]
    (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (k : ℕ) (ρ : Measure (α × ℝ))
    (δ D a ζ : ℝ) where
  ρH : Measure (α × ℝ)
  ρH_le : ρH ≤ ρ
  n : ℕ
  A : Fin n → Set α
  q : Fin n → Fin 3 → ℤ
  h : Fin n → Fin 6 → ℝ
  layer : LayerAt N d e₀ π b k δ ρH D a n A q h
  σ : Measure (α × ℝ)
  σ_le : σ ≤ ρH
  σ_mass : ENNReal.ofReal (N k ^ (-δ)) ≤ σ univ
  F : Fin n → ℝ → Fin 2 → ℝ
  E : Fin n → Set (α × ℝ)
  measurable_F : ∀ i, Measurable (F i)
  bound_F : ∀ i t e, |F i t e| ≤ N k ^ δ
  measurableSet_E : ∀ i, MeasurableSet (E i)
  E_sub : ∀ i, E i ⊆ A i ×ˢ Icc (0 : ℝ) 1
  conull : ∀ i, σ ((A i ×ˢ Icc (0 : ℝ) 1) \ E i) = 0
  support : ∀ i (t w : ℝ), ζ ≤ w → w ≤ 1 →
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ N k ^ δ * w ^ (-d) ∧
      ∀ l, (l, t) ∈ E i →
        ⌊FirstJet.scal (RawChart.y ⟨A i, q i, h i, F i, E i⟩ (b k) a D)
          (RawChart.β ⟨A i, q i, h i, F i, E i⟩ (b k) a D)
          (RawChart.γ ⟨A i, q i, h i, F i, E i⟩ (b k) a D) (F i) l t / w⌋ ∈ C

/-- The comparison half for one prepared input: at every target depth `s < sMax` and every
loss `δ`, eventually a compared layer at the old depth `s₀ = s/(1+θ)` with the reading floor
of `RawChartsAt`. -/
def ComparedLayersAt (N : ℕ → ℝ) (d e₀ u θ sMax : ℝ) {α : Type} [MeasurableSpace α]
    (ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s < sMax → ∀ δ : ℝ, 0 < δ →
    let s₀ := s / (1 + θ)
    let c := θ * s₀
    ∀ᶠ k in atTop, Nonempty (ComparedLayer N d e₀ π b k (ρ k) δ (N k ^ (-u * s₀))
      (N k ^ (-s₀)) ((N k ^ (-c)) ^ (1000 / (1 - d))))

/-- The comparison half for every prepared input with the same structural constants. -/
def ComparedEngineAt (d κ ℓ S U e₀ u θ sMax : ℝ) : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop →
    ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε) →
    ∀ (α : Type) [MeasurableSpace α] (ν : ℕ → Measure α) (μ ρ : ℕ → Measure (α × ℝ))
      (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ)
      (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
      (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α)
      (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ)
      (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ),
      Hyp1 K ν μ ρ π b P → Hyp2 N K d S μ π b P →
      Hyp3 N K d κ ℓ U e₀ ν μ π b P T n j A B c F → Hyp4 U T n j A →
      ComparedLayersAt N d e₀ u θ sMax ρ π b

/-- The comparison half of the strict step, with the same quantifier structure as
`RawStepPreparation`. -/
def ComparedStep : Prop :=
  ScalarInput → RowInput → MatchingInput →
    ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → 2 * κ < 1 → ℓ = κ →
      0 < S → S ≤ 1 → 0 < U → 0 < e₀ →
      ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ sMax : ℝ, 0 < sMax → sMax ≤ s₁ →
        ∀ u θ : ℝ, 2 * κ < u → u ≤ 1 → 0 < θ →
          θ ≤ (1 - d) / 10000 * (u - 2 * κ) →
          EngineAt d κ ℓ S U e₀ u sMax → ComparedEngineAt d κ ℓ S U e₀ u θ sMax

end

end Submission.Obl.k4_horizontal_strict_parameter_step
