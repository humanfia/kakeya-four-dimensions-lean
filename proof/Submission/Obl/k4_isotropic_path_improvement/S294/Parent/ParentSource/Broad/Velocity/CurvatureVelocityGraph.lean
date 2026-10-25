-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.CurvatureVelocityGraph, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/CurvatureVelocityGraph.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/CurvatureVelocityGraph.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o265, Broad/Velocity/NativeVelocityGraph.lean,
-- inherited from o106/x0352, commit d78c43c7c261. The row-selection and
-- original-law accounting are reused; only the geometric value assumption
-- is replaced by the actual leading-coefficient bound.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.NativeVelocityGraph
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CurvatureBroadMass

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open MeasureTheory Set SourceGeometry
open Submission.Obl.k4_mk_grid_transfer
open scoped ENNReal
noncomputable section

namespace AnisotropicVelocityData
variable {X : Type*} [MeasurableSpace X]

structure CurvatureValid (a : AnisotropicVelocityData X) : Prop where
  priorFinite : IsFiniteMeasure a.prior
  incidenceFinite : IsFiniteMeasure a.incidence
  cellInjective : Function.Injective a.cell
  weightMeas : Measurable a.weight
  codeMeas : Measurable a.code
  bound_ge : 1 ≤ a.bound
  mesh_pos : 0 < a.baseMesh
  mesh_ge : a.baseMesh ≤ a.mesh
  liftRho_pos : 0 < a.liftRho
  baseRho_nonneg : 0 ≤ a.baseRho
  fraction_nonneg : 0 ≤ a.fraction
  fraction_lt : a.fraction < a.baseFraction
  timeVelocity : ∀ x, a.velocity x 0 = 1
  quadratic : ∀ x t, MvPolynomial.eval (fun j => a.position x j + t * a.velocity x j) (a.test x) =
    a.qa x * t ^ 2 + a.qb x * t + a.qc x
  curvature : ∀ x, |a.qa x| ≤ 8 * a.bound
  anchorMeas : Measurable (fun x => a.baseMesh⁻¹ • heightScale (a.baseMesh / a.mesh) (nativePhysicalCurve
    (a.test x) (a.position x) (a.velocity x) a.anchor))
  tangentMeas : Measurable (fun x => liftedVector (fun j => a.velocity x j.castSucc)
    (2 * a.qa x * a.anchor + a.qb x))
  directionMeas : Measurable a.direction
  tangentError : 8 * a.bound * a.window ^ 2 < a.mesh
  directionError : 32 * a.bound * a.window ≤ a.liftRho / 2
  density : ∀ x t, a.weight (x, t) ≤ ENNReal.ofReal a.bound
  support : ∀ x t, a.weight (x, t) ≠ 0 → |t - a.anchor| ≤ a.window ∧
    a.baseMesh⁻¹ • heightScale (a.baseMesh / a.mesh) (nativePhysicalCurve (a.test x) (a.position x) (a.velocity x) t) ∈
      latticeCell (a.cell (a.code (x, t)))
  priorCap : a.prior.real univ ≤ a.bound * a.priorScale / a.mesh ^ ((2 : ℝ) / 3)
  supportCount : (a.cells : ℝ) ≤ a.bound *
    (a.mesh ^ ((2 : ℝ) / 3) / a.baseMesh) ^ 3 * (a.mesh ^ ((2 : ℝ) / 3) / a.mesh) ^ a.dimension
  boundedMeas : MeasurableSet a.bounded
  boundedFull : a.incidence a.boundedᶜ = 0
  baseBound : ∀ q ∈ a.bounded, ∀ j, |a.base q j| ≤ a.bound
  scalarBound : ∀ q ∈ a.bounded, |a.scalar q| ≤ a.bound
  rawBound : ∀ q ∈ a.bounded, ‖liftedVector (a.base q) (a.scalar q)‖ ≤ a.bound
  baseBroad : ∀ i, cellBroad a.incidence a.code a.base a.baseRho a.baseFraction i
  conditioned : 1 ≤ a.bound * a.baseRho ^ 3
  small : 36 * a.bound ^ 3 * (a.bound * a.liftRho) ≤ 1

end AnisotropicVelocityData

theorem anisotropic_native_velocity_graph_of_curvature :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X],
      ∀ a : AnisotropicVelocityData X, a.CurvatureValid →
      ∃ (G : Fin a.cells → Fin 3 → ℝ) (T : Set (X × ℝ)),
        MeasurableSet T ∧ Measurable (fun q => G (a.code q)) ∧
        (∀ i j, |G i j| ≤ 28 * a.bound ^ 6) ∧
        a.incidence.real Tᶜ ≤ a.broadMass + a.fraction * a.incidence.real univ ∧
        (a.fraction * a.liftRho / 4) ^ 4 * a.broadMass ^ 4 ≤
          256 * C ^ 3 * a.bound ^ 9 * a.priorScale ^ 4 * a.mesh ^ ((1 - a.dimension) / 3) ∧
        ∀ q ∈ T, q ∈ a.bounded ∧
          |a.scalar q - ∑ j, G (a.code q) j * a.base q j| ≤ 80 * a.bound ^ 7 * a.liftRho := by
  obtain ⟨C, hC, hmoment⟩ := anisotropic_native_broad_code_moment_of_curvature
  refine ⟨C, hC, ?_⟩
  intro X instX a ha
  let _ : IsFiniteMeasure a.prior := ha.priorFinite
  let _ : IsFiniteMeasure a.incidence := ha.incidenceFinite
  let _ : IsFiniteMeasure ((a.prior.prod volume).withDensity a.weight) := ha.incidenceFinite
  have hK : 0 < a.bound := by linarith [ha.bound_ge]
  have hmomentA := hmoment a.cells a.cell ha.cellInjective a.prior a.test a.position a.velocity
    a.qa a.qb a.qc a.anchor a.window a.bound a.baseMesh a.mesh a.liftRho a.fraction a.priorScale a.dimension
    a.weight ha.weightMeas a.code ha.codeMeas hK ha.mesh_pos ha.mesh_ge ha.liftRho_pos ha.fraction_nonneg
    ha.timeVelocity ha.quadratic ha.curvature ha.anchorMeas ha.tangentMeas ha.tangentError
    ha.directionError ha.density ha.support ha.priorCap ha.supportCount
  obtain ⟨G, T, hT, hGmeas, hG, hloss, hfit⟩ := rows_outside_broad_cells_on a.incidence
    a.code ha.codeMeas a.bounded ha.boundedMeas ha.boundedFull a.base a.scalar ha.directionMeas
    a.baseRho a.liftRho a.fraction a.baseFraction a.bound ha.baseRho_nonneg ha.liftRho_pos.le
    ha.fraction_nonneg ha.fraction_lt ha.bound_ge ha.baseBound ha.scalarBound ha.rawBound
    ha.baseBroad ha.conditioned ha.small
  exact ⟨G, T, hT, hGmeas, hG, hloss, hmomentA, hfit⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
