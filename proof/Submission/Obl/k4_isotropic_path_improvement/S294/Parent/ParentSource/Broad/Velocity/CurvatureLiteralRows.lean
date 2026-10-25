-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.CurvatureLiteralRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/CurvatureLiteralRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/CurvatureLiteralRows.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o265, Broad/Velocity/LiteralRows.lean.
-- The original proof and original full-reference moments are retained;
-- the graph engine now accepts arbitrary constant signal offsets.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.LiteralRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CurvatureVelocityGraph

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open Set MeasureTheory
noncomputable section

theorem anisotropic_native_literal_rows_of_curvature :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type} [MeasurableSpace X],
      ∀ a : AnisotropicVelocityData X, a.CurvatureValid →
      ∀ (state : X × ℝ → Fin 4 → ℤ) (P : Set (X × ℝ)),
        (∀ q ∈ P, a.cell (a.code q) = state q) →
      ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (T : Set (X × ℝ)),
        Measurable row ∧ MeasurableSet T ∧ (∀ q j, |row q j| ≤ 28 * a.bound ^ 6) ∧
        a.incidence.real Tᶜ ≤ a.broadMass + a.fraction * a.incidence.real univ ∧
        (a.fraction * a.liftRho / 4) ^ 4 * a.broadMass ^ 4 ≤
          256 * C ^ 3 * a.bound ^ 9 * a.priorScale ^ 4 * a.mesh ^ ((1 - a.dimension) / 3) ∧
        ∀ q ∈ T ∩ P, q ∈ a.bounded ∧
          |a.scalar q - ∑ j, row (state q) j * a.base q j| ≤ 80 * a.bound ^ 7 * a.liftRho := by
  obtain ⟨C, hC, hgraph⟩ := anisotropic_native_velocity_graph_of_curvature
  refine ⟨C, hC, ?_⟩
  intro X instX a ha state P hstate
  obtain ⟨G, T, hT, hGmeas, hG, hloss, hmoment, hfit⟩ := hgraph a ha
  obtain ⟨row, hrowMeas, hrow, heq⟩ := exists_literal_row_extension a.cell ha.cellInjective G
    (by positivity : 0 ≤ 28 * a.bound ^ 6) hG
  refine ⟨row, T, hrowMeas, hT, hrow, hloss, hmoment, ?_⟩
  intro q hq
  have hh := hfit q hq.1
  rw [← hstate q hq.2, heq]
  exact hh

/-- One constant is fixed for every original packet, before the source,
the path and its assigned-line subtype are chosen. -/
def curvatureRowConstant : ℝ := Classical.choose anisotropic_native_literal_rows_of_curvature

theorem curvatureRowConstant_pos : 0 < curvatureRowConstant :=
  (Classical.choose_spec anisotropic_native_literal_rows_of_curvature).1

theorem curvature_literal_rows_fixed {X : Type} [MeasurableSpace X]
    (a : AnisotropicVelocityData X) (ha : a.CurvatureValid)
    (state : X × ℝ → Fin 4 → ℤ) (P : Set (X × ℝ))
    (hstate : ∀ q ∈ P, a.cell (a.code q) = state q) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (T : Set (X × ℝ)),
      Measurable row ∧ MeasurableSet T ∧ (∀ q j, |row q j| ≤ 28 * a.bound ^ 6) ∧
      a.incidence.real Tᶜ ≤ a.broadMass + a.fraction * a.incidence.real univ ∧
      (a.fraction * a.liftRho / 4) ^ 4 * a.broadMass ^ 4 ≤
        256 * curvatureRowConstant ^ 3 * a.bound ^ 9 * a.priorScale ^ 4 *
          a.mesh ^ ((1 - a.dimension) / 3) ∧
      ∀ q ∈ T ∩ P, q ∈ a.bounded ∧
        |a.scalar q - ∑ j, row (state q) j * a.base q j| ≤ 80 * a.bound ^ 7 * a.liftRho :=
  (Classical.choose_spec anisotropic_native_literal_rows_of_curvature).2 a ha state P hstate

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
