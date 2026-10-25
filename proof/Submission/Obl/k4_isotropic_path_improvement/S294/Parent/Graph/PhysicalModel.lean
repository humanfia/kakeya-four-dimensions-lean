-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.PhysicalModel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/PhysicalModel.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). A physical velocity model for an arbitrary quadratic test on
an arbitrary family of lines, in the lines' own coordinates.

This is the frame-free form of `originalNativeModel` (this LOT tree, o265,
session x0943, Broad/Source/OriginalNativeModel.lean and
OriginalNativeValidity.lean): the test, the line positions and velocities
and the quadratic coefficients are parameters, so the parent quadratic `P`
can be used in original time and original physical coordinates.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.LiteralRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CoarseDuration
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.StripSubspaces
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FiniteStateLaws
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AssignedGridGeometry

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_mk_grid_transfer
open scoped ENNReal

noncomputable section

variable {X : Type} [MeasurableSpace X]

/-- The fine physical code of an incidence for the test `P0`: base mesh in
the first three curve coordinates, `hidden` in the test value. -/
def physCode (P0 : MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ) (baseMesh hidden : ℝ)
    (z : X × ℝ) : Fin 4 → ℤ :=
  fun j => ⌊nativePhysicalCurve P0 (p z.1) (v z.1) z.2 j / (if j = 3 then hidden else baseMesh)⌋

theorem measurable_physCode (P0 : MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ)
    (hcurve : Measurable (fun z : X × ℝ => nativePhysicalCurve P0 (p z.1) (v z.1) z.2))
    (baseMesh hidden : ℝ) : Measurable (physCode P0 p v baseMesh hidden) := by
  apply measurable_pi_iff.mpr
  intro j
  exact Int.measurable_floor.comp
    (((PiLp.continuous_apply 2 _ j).measurable.comp hcurve).div_const _)

theorem physCode_mem_latticeCell (P0 : MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ)
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden) (z : X × ℝ) :
    baseMesh⁻¹ • heightScale (baseMesh / hidden)
        (nativePhysicalCurve P0 (p z.1) (v z.1) z.2) ∈
      latticeCell (physCode P0 p v baseMesh hidden z) :=
  anisotropic_point_mem_latticeCell hbase hhidden _

/-- The coarse cell source: events of `E` in the coarse cell `q`. -/
def coarseCellSource (P0 : MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ) (coarse : ℝ)
    (E : Set (X × ℝ)) (q : Fin 4 → ℤ) : Set (X × ℝ) :=
  E ∩ nativeCoarseCode P0 p v coarse ⁻¹' {q}

/-- The physical velocity model of one coarse cell. The prior keeps the
lines with an EARLIER duration witness in the cell; the incidences are those
of the current set in the cell. -/
def cellModel (ν : Measure X) (P0 : MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ)
    (qa qb qc : X → ℝ) (earlier current : Set (X × ℝ)) (coarse : ℝ) (q : Fin 4 → ℤ)
    (baseMesh hidden lossRate K liftRho baseRho fraction baseFraction dimension : ℝ)
    {n : ℕ} (code : X × ℝ → Fin n) (cell : Fin n → Fin 4 → ℤ) :
    AnisotropicVelocityData X where
  cells := n
  cell := cell
  prior := ν.restrict {x | ENNReal.ofReal (lossRate * coarse) ≤
    incidenceDuration (coarseCellSource P0 p v coarse earlier q) x}
  test := fun _ => P0
  position := p
  velocity := v
  qa := qa
  qb := qb
  qc := qc
  anchor := coarse * ((q 0 : ℝ) + 1 / 2)
  window := coarse
  bound := K
  mesh := hidden
  baseMesh := baseMesh
  liftRho := liftRho
  baseRho := baseRho
  fraction := fraction
  baseFraction := baseFraction
  priorScale := (ν.prod volume).real (coarseCellSource P0 p v coarse earlier q)
  dimension := dimension
  weight := (coarseCellSource P0 p v coarse current q).indicator (fun _ => 1)
  code := code
  bounded := univ ×ˢ Icc (0 : ℝ) 1

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_mk_grid_transfer
open scoped ENNReal

noncomputable section

variable {X : Type} [MeasurableSpace X]

theorem measurable_nativeCoarseCode (P0 : MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ)
    (hcurve : Measurable (fun z : X × ℝ => nativePhysicalCurve P0 (p z.1) (v z.1) z.2))
    (coarse : ℝ) : Measurable (nativeCoarseCode P0 p v coarse) := by
  apply measurable_pi_iff.mpr
  intro j
  exact Int.measurable_floor.comp
    (((PiLp.continuous_apply 2 _ j).measurable.comp hcurve).div_const coarse)

theorem measurableSet_coarseCellSource (P0 : MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ)
    (hcurve : Measurable (fun z : X × ℝ => nativePhysicalCurve P0 (p z.1) (v z.1) z.2))
    (coarse : ℝ) {E : Set (X × ℝ)} (hE : MeasurableSet E) (q : Fin 4 → ℤ) :
    MeasurableSet (coarseCellSource P0 p v coarse E q) :=
  hE.inter (measurable_nativeCoarseCode P0 p v hcurve coarse (measurableSet_singleton q))

/-- The model's incidence is the original incidence law on the current cell. -/
theorem cellModel_incidence (ν : Measure X) [SFinite ν] (P0 : MvPolynomial (Fin 4) ℝ)
    (p v : X → Fin 4 → ℝ)
    (hcurve : Measurable (fun z : X × ℝ => nativePhysicalCurve P0 (p z.1) (v z.1) z.2))
    (qa qb qc : X → ℝ) (earlier current : Set (X × ℝ)) (hcurrent : MeasurableSet current)
    (coarse : ℝ) (q : Fin 4 → ℤ)
    (baseMesh hidden lossRate K liftRho baseRho fraction baseFraction dimension : ℝ)
    {n : ℕ} (code : X × ℝ → Fin n) (cell : Fin n → Fin 4 → ℤ)
    (hlong : ∀ z ∈ coarseCellSource P0 p v coarse current q,
      ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (coarseCellSource P0 p v coarse earlier q) z.1) :
    (cellModel ν P0 p v qa qb qc earlier current coarse q baseMesh hidden lossRate K liftRho
      baseRho fraction baseFraction dimension code cell).incidence =
        (ν.prod volume).restrict (coarseCellSource P0 p v coarse current q) := by
  have hev : MeasurableSet (coarseCellSource P0 p v coarse current q) :=
    measurableSet_coarseCellSource P0 p v hcurve coarse hcurrent q
  change (((ν.restrict _).prod volume).withDensity
    ((coarseCellSource P0 p v coarse current q).indicator (fun _ => 1))) = _
  rw [withDensity_indicator hev, withDensity_const, one_smul]
  exact restrict_prior_incidence_eq _ _ _ hev (fun z hz => ⟨hlong z hz, mem_univ _⟩)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry

theorem measurable_physCurve {X : Type} [MeasurableSpace X] (P0 : MvPolynomial (Fin 4) ℝ)
    (p v : X → Fin 4 → ℝ) (hpm : Measurable p) (hvm : Measurable v) :
    Measurable (fun z : X × ℝ => nativePhysicalCurve P0 (p z.1) (v z.1) z.2) := by
  unfold nativePhysicalCurve liftedVector
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j
  · exact ((measurable_pi_apply _).comp (hpm.comp measurable_fst)).add
      (measurable_snd.mul ((measurable_pi_apply _).comp (hvm.comp measurable_fst)))
  · exact ((measurable_pi_apply _).comp (hpm.comp measurable_fst)).add
      (measurable_snd.mul ((measurable_pi_apply _).comp (hvm.comp measurable_fst)))
  · exact ((measurable_pi_apply _).comp (hpm.comp measurable_fst)).add
      (measurable_snd.mul ((measurable_pi_apply _).comp (hvm.comp measurable_fst)))
  · exact (MvPolynomial.continuous_eval P0).measurable.comp
      (measurable_pi_iff.mpr fun j => ((measurable_pi_apply j).comp (hpm.comp measurable_fst)).add
        (measurable_snd.mul ((measurable_pi_apply j).comp (hvm.comp measurable_fst))))

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
