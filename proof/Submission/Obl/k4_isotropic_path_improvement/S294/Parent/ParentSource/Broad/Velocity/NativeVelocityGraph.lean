-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.NativeVelocityGraph, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/NativeVelocityGraph.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/NativeVelocityGraph.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit d78c43c7c261;
-- source Submission/Obl/k4_isotropic_path_improvement/NativeVelocityGraph.lean.
-- The base and hidden meshes are independent; the MK4 determinant retains
-- one compression factor as proved in HeightScale and NativeBroadMass.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.NativeBroadMass
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.VelocityGraph

/-!
The complete conditional native physical velocity-graph step. Actual
quadratic trajectories and one original incidence law are the data; the
only geometric inputs are base breadth, the prior cap and the physical
support count. No capturing plane or broad-state certificate is supplied.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set
open SourceGeometry
open scoped ENNReal
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

structure AnisotropicVelocityData (X : Type*) [MeasurableSpace X] where
  cells : ℕ
  cell : Fin cells → Fin 4 → ℤ
  prior : Measure X
  test : X → MvPolynomial (Fin 4) ℝ
  position : X → Fin 4 → ℝ
  velocity : X → Fin 4 → ℝ
  qa : X → ℝ
  qb : X → ℝ
  qc : X → ℝ
  anchor : ℝ
  window : ℝ
  bound : ℝ
  mesh : ℝ
  baseMesh : ℝ
  liftRho : ℝ
  baseRho : ℝ
  fraction : ℝ
  baseFraction : ℝ
  priorScale : ℝ
  dimension : ℝ
  weight : X × ℝ → ENNReal
  code : X × ℝ → Fin cells
  bounded : Set (X × ℝ)

namespace AnisotropicVelocityData

variable {X : Type*} [MeasurableSpace X]

def incidence (a : AnisotropicVelocityData X) : Measure (X × ℝ) :=
  (a.prior.prod volume).withDensity a.weight

def base (a : AnisotropicVelocityData X) (q : X × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun j => a.velocity q.1 j.castSucc)

def scalar (a : AnisotropicVelocityData X) (q : X × ℝ) : ℝ := 2 * a.qa q.1 * q.2 + a.qb q.1

def direction (a : AnisotropicVelocityData X) (q : X × ℝ) : EuclideanSpace ℝ (Fin 4) :=
  unitTangent (liftedVector (a.base q) (a.scalar q))

/-- These are bounds on actual native trajectories and their original
physical cell laws, before the graph reference is selected. -/
structure Valid (a : AnisotropicVelocityData X) : Prop where
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
  whole : ∀ x t, t ∈ Icc (0 : ℝ) 1 →
    |MvPolynomial.eval (fun j => a.position x j + t * a.velocity x j) (a.test x)| ≤ a.bound
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

def broadMass (a : AnisotropicVelocityData X) : ℝ :=
  a.incidence.real {q | cellBroad a.incidence a.code a.direction a.liftRho a.fraction (a.code q)}

end AnisotropicVelocityData

/-- A uniform physical graph theorem with the original broad-cell mass
and its full native Kakeya moment, including arbitrary non-atomic priors. -/
theorem anisotropic_native_velocity_graph :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X],
      ∀ a : AnisotropicVelocityData X, a.Valid →
      ∃ (G : Fin a.cells → Fin 3 → ℝ) (T : Set (X × ℝ)),
        MeasurableSet T ∧ Measurable (fun q => G (a.code q)) ∧
        (∀ i j, |G i j| ≤ 28 * a.bound ^ 6) ∧
        a.incidence.real Tᶜ ≤ a.broadMass + a.fraction * a.incidence.real univ ∧
        (a.fraction * a.liftRho / 4) ^ 4 * a.broadMass ^ 4 ≤
          256 * C ^ 3 * a.bound ^ 9 * a.priorScale ^ 4 * a.mesh ^ ((1 - a.dimension) / 3) ∧
        ∀ q ∈ T, q ∈ a.bounded ∧
          |a.scalar q - ∑ j, G (a.code q) j * a.base q j| ≤ 80 * a.bound ^ 7 * a.liftRho := by
  obtain ⟨C, hC, hmoment⟩ := anisotropic_native_broad_code_moment
  refine ⟨C, hC, ?_⟩
  intro X instX a ha
  let _ : IsFiniteMeasure a.prior := ha.priorFinite
  let _ : IsFiniteMeasure a.incidence := ha.incidenceFinite
  let _ : IsFiniteMeasure ((a.prior.prod volume).withDensity a.weight) := ha.incidenceFinite
  have hK : 0 < a.bound := by linarith [ha.bound_ge]
  have hmomentA := hmoment a.cells a.cell ha.cellInjective a.prior a.test a.position a.velocity
    a.qa a.qb a.qc a.anchor a.window a.bound a.baseMesh a.mesh a.liftRho a.fraction a.priorScale a.dimension
    a.weight ha.weightMeas a.code ha.codeMeas hK ha.mesh_pos ha.mesh_ge ha.liftRho_pos ha.fraction_nonneg
    ha.timeVelocity ha.quadratic ha.whole ha.anchorMeas ha.tangentMeas ha.tangentError
    ha.directionError ha.density ha.support ha.priorCap ha.supportCount
  obtain ⟨G, T, hT, hGmeas, hG, hloss, hfit⟩ := rows_outside_broad_cells_on a.incidence
    a.code ha.codeMeas a.bounded ha.boundedMeas ha.boundedFull a.base a.scalar ha.directionMeas
    a.baseRho a.liftRho a.fraction a.baseFraction a.bound ha.baseRho_nonneg ha.liftRho_pos.le
    ha.fraction_nonneg ha.fraction_lt ha.bound_ge ha.baseBound ha.scalarBound ha.rawBound
    ha.baseBroad ha.conditioned ha.small
  exact ⟨G, T, hT, hGmeas, hG, hloss, hmomentA, hfit⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
