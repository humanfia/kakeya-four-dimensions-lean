import Submission.Obl.k4_row_incidence_graph_construction.FiniteInput

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_row_incidence_graph_construction

-- IncidenceData and its indexing maps are adapted from this LOT tree, o063,
-- session x0213, Interfaces.lean (e15ca2d), as retained in split s025.

def trajectoryPosition {α : Type*} (b v : α → ℝ) (p : α × ℝ) : Fin 2 → ℝ :=
  ![p.2, b p.1 + p.2 * v p.1]

noncomputable def positionIndex {α : Type*} (h : ℝ) (b v : α → ℝ)
    (p : α × ℝ) : Fin 2 → ℤ := fun j => ⌊trajectoryPosition b v p j / h⌋

/-- Exactly the incidence hypotheses of the frozen row-fit assertion. -/
structure IncidenceData (S a η N : ℝ) (α : Type) [MeasurableSpace α] where
  prior : Measure α
  active : Measure (α × ℝ)
  intercept : α → ℝ
  velocity : α → ℝ
  evaluation : α → ℝ
  row : α × ℝ → Fin 2 → ℝ
  palette : Measure ℝ
  error : ℝ
  bins : (Fin 2 → ℤ) → Finset (Fin 2 → ℤ)
  measurable_intercept : Measurable intercept
  measurable_velocity : Measurable velocity
  measurable_evaluation : Measurable evaluation
  measurable_row : Measurable row
  prior_probability : IsProbabilityMeasure prior
  palette_probability : IsProbabilityMeasure palette
  error_lower : N ^ (-a) ≤ error
  error_upper : error ≤ 1
  trajectory_bound : ∀ l, |intercept l| + |velocity l| ≤ N ^ η
  domination : active ≤ ENNReal.ofReal (N ^ η) • (prior.prod volume)
  time_support : active (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0
  mass_lower : ENNReal.ofReal (N ^ (-η)) ≤ active univ
  palette_cap : ∀ x r : ℝ, N ^ (-a) ≤ r → r ≤ 1 →
    palette (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)
  joint_cap : ∀ (q : Fin 2 → ℤ) (j : ℤ),
    active {p | positionIndex (N ^ (-a)) intercept velocity p = q ∧
      ⌊velocity p.1 / (N ^ (-a))⌋ = j} ≤
      ENNReal.ofReal (N ^ η * (N ^ (-a)) ^ 2) *
        palette (Ico ((j : ℝ) * (N ^ (-a))) (((j : ℝ) + 1) * (N ^ (-a))))
  bins_card : ∀ q, ((bins q).card : ℝ) ≤ N ^ η
  row_constraint : ∀ᵐ p ∂active, (∀ j, |row p j| ≤ N ^ η) ∧
    (fun j => ⌊row p j / error⌋) ∈ bins (positionIndex (N ^ (-a)) intercept velocity p) ∧
    |row p 0 + velocity p.1 * row p 1 - evaluation p.1| ≤ N ^ η * error

/-- The regularized table, retaining witnesses in the original measure. -/
structure RegularizedData {S a η N : ℝ} {α : Type} [MeasurableSpace α]
    (d : IncidenceData S a η N α) (ε : ℝ) where
  base : ℝ
  separation : ℝ
  base_lower : 1 ≤ base
  separation_lower : 2 ≤ separation
  base_le_separation : base ≤ separation
  subpower : separation ≤ N ^ ε
  domination : d.active ≤ ENNReal.ofReal base • (d.prior.prod volume)
  finite : FiniteIncidenceData (N ^ (-a)) base separation (S / 4)
  cells : CellWitnessData d.active (trajectoryPosition d.intercept d.velocity) d.row
    (N ^ (-a)) d.error base separation (S / 4) finite

/-- The measure stage, before any directions or graphs are selected. -/
def CellRegularization : Prop :=
  ∀ S a ε : ℝ, 0 < S → 0 < a → 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
    ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α],
    ∀ d : IncidenceData S a η N α, Nonempty (RegularizedData d ε)

end Submission.Obl.k4_row_incidence_graph_construction
