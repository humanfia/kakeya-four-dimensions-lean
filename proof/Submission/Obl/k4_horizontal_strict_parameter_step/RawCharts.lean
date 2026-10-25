import Submission.Obl.k4_horizontal_strict_parameter_step.Regularization
import Submission.Obl.k4_horizontal_strict_parameter_step.ChartCoordinates

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/RawCharts.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- One old full-time chart, its selected time row, and its current labeled event.
All normalized coordinates are defined on the original trajectory type. -/
structure RawChart (α : Type) where
  A : Set α
  q : Fin 3 → ℤ
  h : Fin 6 → ℝ
  F : ℝ → Fin 2 → ℝ
  E : Set (α × ℝ)

namespace RawChart

variable {α : Type} [MeasurableSpace α] (C : RawChart α)

def prior (ν : Measure α) : Measure α := (ν C.A)⁻¹ • ν.restrict C.A

def coordinates (b : α → Fin 6 → ℝ) (a D : ℝ) : α → Fin 4 → ℝ :=
  chartCoordinates C.A b C.h a D ((C.q 1 : ℝ) * D) ((C.q 2 : ℝ) * D)

def y (b : α → Fin 6 → ℝ) (a D : ℝ) (l : α) : Fin 2 → ℝ :=
  ![C.coordinates b a D l 0, C.coordinates b a D l 1]

def β (b : α → Fin 6 → ℝ) (a D : ℝ) (l : α) : ℝ := C.coordinates b a D l 2

def γ (b : α → Fin 6 → ℝ) (a D : ℝ) (l : α) : ℝ := C.coordinates b a D l 3

/-- The raw geometric chart properties needed for restoration after a first-jet call.
The density lower bound is in the original current law and uses the same original
assignment mass as the conditional trajectory prior. -/
structure Valid (ν : Measure α) (ρ : Measure (α × ℝ)) (b : α → Fin 6 → ℝ)
    (d N ε χ D a ζ : ℝ) : Prop where
  measurable_A : MeasurableSet C.A
  prior_pos : 0 < ν C.A
  probability : IsProbabilityMeasure (C.prior ν)
  grid : ∀ l ∈ C.A, ⌊b l 3 / χ⌋ = C.q 0 ∧
    ⌊b l 0 / D⌋ = C.q 1 ∧ ⌊b l 1 / D⌋ = C.q 2
  norm : ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ p ∈ Icc ((C.q 1 : ℝ) * D) (((C.q 1 : ℝ) + 1) * D),
    ∀ q ∈ Icc ((C.q 2 : ℝ) * D) (((C.q 2 : ℝ) + 1) * D),
      |predictor C.h t p q| ≤ N ^ ε
  fit : ∀ l ∈ C.A, ∀ t ∈ Icc (0 : ℝ) 1,
    |b l 2 + t * b l 5 - predictor C.h t (b l 0) (b l 1)| ≤ N ^ ε * a
  labeled : C.E ⊆ C.A ×ˢ Icc (0 : ℝ) 1
  lower : (ENNReal.ofReal (N ^ (-ε)) * ν C.A) •
    (((C.prior ν).prod volume).restrict C.E) ≤ ρ.restrict (C.A ×ˢ Icc (0 : ℝ) 1)
  data : UnregularizedChart (C.prior ν) (C.y b a D) (C.β b a D) (C.γ b a D)
    C.E C.F d (N ^ ε) ζ

end RawChart

/-- A dense disjoint collection of raw charts with a bounded total numerator budget.
The first-jet output only refines each old assignment. -/
structure RawChartFamily (α : Type) [MeasurableSpace α] (ν : Measure α)
    (ρ : Measure (α × ℝ)) (π : Measure ℝ) (b : α → Fin 6 → ℝ)
    (d N ε χ D a ζ : ℝ) where
  n : ℕ
  chart : Fin n → RawChart α
  valid : ∀ i, (chart i).Valid ν ρ b d N ε χ D a ζ
  disjoint : ∀ i j, i ≠ j → Disjoint (chart i).A (chart j).A
  dense_prior : ENNReal.ofReal (N ^ (-ε)) ≤ ∑ i, ν (chart i).A
  numerator_budget : (∑ i, ENNReal.ofReal (D ^ 2 * a ^ d) *
    π (Ico (((chart i).q 0 : ℝ) * χ) ((((chart i).q 0 : ℝ) + 1) * χ))) ≤
      ENNReal.ofReal (N ^ ε)

end

end Submission.Obl.k4_horizontal_strict_parameter_step
