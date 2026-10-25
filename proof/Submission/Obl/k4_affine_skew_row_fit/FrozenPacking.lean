import Submission.Obl.k4_affine_skew_row_fit.Interfaces
import Submission.Obl.k4_retained_edge_planar_rigidity
import Submission.Obl.k4_row_incidence_graph_construction

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_affine_skew_row_fit

/-- Package the fully expanded frozen planar child into its concrete interface. -/
theorem planar_rigidity_of_frozen
    (hdecay : (∀ s : ℝ, 0 < s → s ≤ 1 → ∃ n : ℕ, 2 ≤ n ∧ ∃ r₀ ε₀ τ : ℝ, 0 < r₀ ∧ 0 < ε₀ ∧ 0 < τ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ μ : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure μ → μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → (∀ x u : ℝ, r ≤ u → u ≤ 1 → μ (Set.Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε₀) * u ^ s)) → ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ → ‖MeasureTheory.integral (MeasureTheory.Measure.pi (fun _ : Fin n => μ)) (fun x : Fin n → ℝ => Complex.exp (((-2 * Real.pi * ξ * (∏ j : Fin n, x j) : ℝ) : ℂ) * Complex.I))‖ ≤ |ξ| ^ (-τ))) : PlanarRigidity := by
  intro S hS ε hε
  obtain ⟨η, hη, h₀, hh₀, hcore⟩ :=
    Submission.k4_retained_edge_planar_rigidity hdecay S hS ε hε
  refine ⟨η, hη, h₀, hh₀, ?_⟩
  intro h hh hhsmall d
  exact hcore h hh hhsmall d.size d.weight d.ratio d.left d.right d.graph
    d.left_grid d.right_grid d.left_bound d.right_bound d.left_card_lower d.left_card_upper d.right_card_lower d.right_card_upper d.weight_nonneg d.sum_weight d.ratio_bound d.ratio_cap d.graph_subset d.graph_card d.sum_card d.first_coordinate_cap

/-- Package the fully expanded frozen incidence child without strengthening it. -/
theorem graph_reduction_of_frozen : GraphReduction := by
  intro S a θ hS ha hθ
  obtain ⟨η, hη, N₀, hN₀, hgraph⟩ :=
    Submission.k4_row_incidence_graph_construction S a θ hS ha hθ
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α inst d
  obtain ⟨m, w, κ, A, B, G, u₁, u₂, W,
    hp_0, hp_1, hp_2, hp_3, hp_4, hp_5, hp_6, hp_7, hp_8, hp_9, hp_10, hp_11, hp_12, hp_13, hp_14, hp_15, hw_0, hw_1, hw_2, hw_3, hw_4, hw_5, hw_6, hw_7, hw_8⟩ :=
    hgraph N hN α d.prior d.active d.intercept d.velocity d.evaluation d.row
      d.palette d.error d.bins
      d.measurable_intercept d.measurable_velocity d.measurable_evaluation d.measurable_row d.prior_probability d.palette_probability d.error_lower d.error_upper d.trajectory_bound d.domination d.time_support d.mass_lower d.palette_cap d.joint_cap d.bins_card d.row_constraint
  refine ⟨{
    planar := {
      size := m
      weight := w
      ratio := κ
      left := A
      right := B
      graph := G
      left_grid := hp_0
      right_grid := hp_1
      left_bound := hp_2
      right_bound := hp_3
      left_card_lower := hp_4
      left_card_upper := hp_5
      right_card_lower := hp_6
      right_card_upper := hp_7
      weight_nonneg := hp_8
      sum_weight := hp_9
      ratio_bound := hp_10
      ratio_cap := hp_11
      graph_subset := hp_12
      graph_card := hp_13
      sum_card := hp_14
      first_coordinate_cap := hp_15
    }
    v₁ := u₁
    v₂ := u₂
    witness := W
    velocity_bound₁ := hw_0
    velocity_bound₂ := hw_1
    velocity_separation := hw_2
    domination := hw_3
    measurable_witness := hw_4
    disjoint_witness := hw_5
    witness_mass := hw_6
    witness_bounds := hw_7
    witness_projections := hw_8
  }⟩

end Submission.Obl.k4_affine_skew_row_fit
