import Submission.Obl.k4_row_incidence_graph_construction.MeasureInput
import Submission.Obl.k4_row_incidence_graph_construction.Interfaces
import Submission.Obl.k4_row_incidence_graph_construction.Loss
import Submission.Obl.k4_row_cell_regularization
import Submission.Obl.k4_finite_row_graph_assembly

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_row_incidence_graph_construction

/-- Package the measure child without adding any hypothesis or conclusion. -/
theorem cell_regularization_of_frozen : CellRegularization := by
  intro S a ε hS ha hε
  obtain ⟨η, hη, N₀, hN₀, hcore⟩ :=
    Submission.k4_row_cell_regularization S a ε hS ha hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α inst d
  obtain ⟨K, R, P, D, u, c, C, hK, hR, hKR, hRN, hdom,
    hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9,
    hc0, hc1, hc2, hc3, hc4, hc5⟩ :=
    hcore N hN α d.prior d.active d.intercept d.velocity d.evaluation d.row
      d.palette d.error d.bins
      d.measurable_intercept d.measurable_velocity d.measurable_evaluation d.measurable_row d.prior_probability d.palette_probability d.error_lower d.error_upper d.trajectory_bound d.domination d.time_support d.mass_lower d.palette_cap d.joint_cap d.bins_card d.row_constraint
  let f : FiniteIncidenceData (N ^ (-a)) K R (S / 4) := {
    points := P
    directions := D
    velocity := u
    mass := c
    mass_nonneg := hf0
    points_card := hf1
    mass_upper := hf2
    mass_total := hf3
    velocity_bound := hf4
    center_bound := hf5
    position_fiber := hf6
    projection_cover := hf7
    direction_cap := hf8
    near_cap := hf9
  }
  let cw : CellWitnessData d.active (trajectoryPosition d.intercept d.velocity) d.row
      (N ^ (-a)) d.error K R (S / 4) f := {
    cell := C
    measurable_cell := hc0
    disjoint_cell := hc1
    cell_mass := hc2
    bounds := hc3
    position_error := hc4
    row_error := hc5
  }
  exact ⟨{
    base := K
    separation := R
    base_lower := hK
    separation_lower := hR
    base_le_separation := hKR
    subpower := hRN
    domination := hdom
    finite := f
    cells := cw
  }⟩

/-- Package the finite child into the same original-incidence graph interface. -/
theorem finite_assembly_of_frozen {α : Type} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (z T : α × ℝ → Fin 2 → ℝ)
    {h E K R s L : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hK : 1 ≤ K) (hR : 2 ≤ R) (hKR : K ≤ R) (hs : 0 ≤ s)
    (loss : LossBounds K R s L) (f : FiniteIncidenceData h K R s)
    (cw : CellWitnessData μ z T h E K R s f)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume)) :
    Nonempty (RowGraphWitness ν μ z T h E L s) := by
  obtain ⟨m, w, κ, A, B, G, u₁, u₂, W,
    hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15,
    hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8⟩ :=
    Submission.k4_finite_row_graph_assembly h E K R s L hh hh1 hK hR hKR hs
      loss.base loss.ratio loss.endpoint loss.endpoint_count loss.sum_count loss.rectangle loss.directions loss.witness_mass loss.witness_error
      α ν μ z T f.points f.directions f.velocity f.mass cw.cell
      f.mass_nonneg f.points_card f.mass_upper f.mass_total f.velocity_bound f.center_bound f.position_fiber f.projection_cover f.direction_cap f.near_cap
      cw.measurable_cell cw.disjoint_cell cw.cell_mass cw.bounds cw.position_error cw.row_error hdom
  exact ⟨{
    planar := {
      size := m
      weight := w
      ratio := κ
      left := A
      right := B
      graph := G
      left_grid := hp0
      right_grid := hp1
      left_bound := hp2
      right_bound := hp3
      left_card_lower := hp4
      left_card_upper := hp5
      right_card_lower := hp6
      right_card_upper := hp7
      weight_nonneg := hp8
      sum_weight := hp9
      ratio_bound := hp10
      ratio_cap := hp11
      graph_subset := hp12
      graph_card := hp13
      sum_card := hp14
      first_coordinate_cap := hp15
    }
    v₁ := u₁
    v₂ := u₂
    witness := W
    velocity_bound₁ := hw0
    velocity_bound₂ := hw1
    velocity_separation := hw2
    domination := hw3
    measurable_witness := hw4
    disjoint_witness := hw5
    witness_mass := hw6
    witness_bounds := hw7
    witness_projections := hw8
  }⟩

end Submission.Obl.k4_row_incidence_graph_construction
