/- From this LOT obligation o226, session x0810; literal raw interface used by the analytic and geometric proofs. -/
import Submission.Obl.k4_horizontal_supercritical_three_projections.Model
import Submission.Obl.k4_horizontal_supercritical_three_projections.Layers
import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartDefs

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Filter

/-- The original law is carried by bounded contact trajectories. This is an
almost-everywhere statement for the original incidence law, before conditioning. -/
def OriginalGood {α : Type} [MeasurableSpace α]
    (N K : ℕ → ℝ) (e₀ : ℝ) (b : ℕ → α → Fin 6 → ℝ)
    (μ : ℕ → Measure (α × ℝ)) : Prop :=
  ∀ᶠ k in atTop, ∀ᵐ p ∂μ k,
    (∀ e, |b k p.1 e| ≤ 3 * K k) ∧ |b k p.1 0| ≤ K k ∧
      |b k p.1 3| ≤ K k ∧ |b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀)

/-- Literal scalar chart estimates under the unchanged original incidence law.
The only angular slice is a slice of the normalized scalar velocity, and the
external palette is still the original velocity-bin probability. -/
def RawChartData {α : Type} [MeasurableSpace α]
    (N K d s₀ Dexp depth e₀ M ξ : ℝ) (b : α → Fin 6 → ℝ)
    (μ : Measure (α × ℝ)) (π : Measure ℝ) : Prop :=
  let χ := N ^ (-M)
  let D := N ^ (-Dexp)
  let σ := N ^ (-(20 * s₀))
  let a := N ^ (-depth)
  ∀ P Q β : ℤ,
    let A : Set α := {l | |b l 0| ≤ K ∧ |b l 3| ≤ K ∧
      |b l 4 + b l 0| ≤ N ^ (-e₀) ∧ ⌊b l 0 / D⌋ = P ∧
      ⌊b l 1 / D⌋ = Q ∧ ⌊b l 3 / χ⌋ = β}
    let y := fun l t => (b l 1 - (Q : ℝ) * D) / D -
      2 * t * ((b l 0 - (P : ℝ) * D) / D)
    let x := fun l t => b l 2 + t * b l 5
    let z := fun p : α × ℝ => ![⌊p.2 / σ⌋, ⌊y p.1 p.2 / σ⌋]
    let W := (π (Ico ((β : ℝ) * χ) (((β : ℝ) + 1) * χ))).toReal * D ^ 2
    μ (A ×ˢ univ) ≤ ENNReal.ofReal (N ^ ξ * W) ∧
    (∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ depth →
      μ {p | p.1 ∈ A ∧ z p = q ∧ ⌊x p.1 p.2 / N ^ (-r)⌋ = j} ≤
        ENNReal.ofReal (N ^ ξ * σ ^ 2 * (N ^ (-r)) ^ d * W)) ∧
    (∀ (r : ℝ) (q : Fin 2 → ℤ) (j v : ℤ), 0 < r → r ≤ s₀ →
      μ {p | p.1 ∈ A ∧ z p = q ∧ ⌊x p.1 p.2 / a⌋ = j ∧
        ⌊(-2 * ((b p.1 0 - (P : ℝ) * D) / D)) / N ^ (-r)⌋ = v} ≤
        ENNReal.ofReal (N ^ ξ * σ ^ 2 * a ^ d * N ^ (-r) * W)) ∧
    (∃ F : Finset ((Fin 2 → ℤ) × ℤ),
      (F.card : ℝ) * σ ^ 2 ≤ N ^ ξ * a ^ (-d) ∧
      ∀ᵐ p ∂μ, p.1 ∈ A → (z p, ⌊x p.1 p.2 / a⌋) ∈ F)

/-- Raw chart estimates at every requested fixed fine direction depth. -/
def RawPreparation {α : Type} [MeasurableSpace α]
    (N K : ℕ → ℝ) (d s₀ Dexp depth e₀ : ℝ)
    (b : ℕ → α → Fin 6 → ℝ) (μ : ℕ → Measure (α × ℝ))
    (π : ℕ → Measure ℝ) : Prop :=
  OriginalGood N K e₀ b μ ∧
    ∀ M : ℝ, 100 * s₀ < M → ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop,
      RawChartData (N k) (K k) d s₀ Dexp depth e₀ M ξ (b k) (μ k) (π k)

/-- Measure hypotheses for the geometric return, independent of true blocks. -/
def BasicLaws {α : Type} [MeasurableSpace α]
    (N K : ℕ → ℝ) (ν : ℕ → Measure α) (μ ρ : ℕ → Measure (α × ℝ))
    (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) : Prop :=
  ∀ k, Measurable (b k) ∧ IsProbabilityMeasure (ν k) ∧
    IsProbabilityMeasure (π k) ∧ μ k ≤ ENNReal.ofReal (K k) • ((ν k).prod volume) ∧
    ρ k ≤ μ k ∧ μ k (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0

/-- A version of the uniform step with the finite layer data written as
existential variables, as they are in the Mathlib-only frozen child. -/
def RawSingleProjection {α : Type} [MeasurableSpace α]
    (N : ℕ → ℝ) (d depth R M Dexp : ℝ) (b : ℕ → α → Fin 6 → ℝ)
    (π : ℕ → Measure ℝ) (ρ : ℕ → Measure (α × ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop,
    ∀ ζ : Measure (α × ℝ), ζ ≤ ρ k → ENNReal.ofReal (N k ^ (-η)) ≤ ζ univ →
      ∃ (n : ℕ) (C : Fin n → Set α) (q : Fin n → Fin 3 → ℤ)
        (G : Fin n → MvPolynomial (Fin 2) ℝ) (ζ' : Measure (α × ℝ)),
        ζ' ≤ ζ ∧ ENNReal.ofReal (N k ^ (-ε)) ≤ ζ' univ ∧
        (∀ᵐ p ∂ζ', ∃ i, p.1 ∈ C i) ∧
        (ProjectionLayer.mk n C q G).Good (N k) d depth ε R (N k ^ (-M))
          (N k ^ (-Dexp)) (b k) (π k) (ρ k)

theorem singleProjection_of_raw {α : Type} [MeasurableSpace α]
    {N : ℕ → ℝ} {d depth R M Dexp : ℝ} {b : ℕ → α → Fin 6 → ℝ}
    {π : ℕ → Measure ℝ} {ρ : ℕ → Measure (α × ℝ)}
    (h : RawSingleProjection N d depth R M Dexp b π ρ) :
    SingleProjection N d depth R M Dexp b π ρ := by
  intro ε hε
  obtain ⟨η, hη, H⟩ := h ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [H] with k hk
  intro ζ hζ hm
  obtain ⟨n, C, q, G, ζ', hζ', hm', hcov, hgood⟩ := hk ζ hζ hm
  exact ⟨⟨n, C, q, G⟩, ζ', hζ', hm', hcov, hgood⟩

end Submission.Obl.k4_horizontal_supercritical_three_projections
