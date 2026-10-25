-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ClockGridCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ClockGridCoordinates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ClockGridCoordinates.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockCurveDuration
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalCellNeighbors

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4ListedExceptions

noncomputable section

def clockParentCoordinates {W : ℕ} (p : PathData W) (old : Fin p.C)
    (P : Po) (z : Ev) : Fin 4 → ℝ :=
  Fin.snoc (fun j => unshearedPacketBase p old z j) (clockParentSignal p old P z)

def clockParentCode {W : ℕ} (p : PathData W) (old : Fin p.C)
    (P : Po) (mesh : ℝ) (z : Ev) : Fin 4 → ℤ :=
  fun j => ⌊clockParentCoordinates p old P z j/mesh⌋

def flattenClockCode (q : (Fin 3 → ℤ) × ℤ) : Fin 4 → ℤ := Fin.snoc q.1 q.2

theorem flattenClockCode_injective : Function.Injective flattenClockCode := by
  intro q r h
  apply Prod.ext
  · ext j
    simpa only [flattenClockCode,Fin.snoc_castSucc] using congrFun h j.castSucc
  · simpa only [flattenClockCode,Fin.snoc_last] using congrFun h (Fin.last 3)

theorem clockParentCode_eq_product {W : ℕ} (p : PathData W) (old : Fin p.C)
    (P : Po) (mesh : ℝ) (z : Ev) :
    clockParentCode p old P mesh z = flattenClockCode
      (gridCode (fun z j => unshearedPacketBase p old z j)
        (clockParentSignal p old P) mesh mesh z) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [clockParentCode,clockParentCoordinates,flattenClockCode,gridCode,Fin.snoc_last]
  · simp only [clockParentCode,clockParentCoordinates,flattenClockCode,gridCode,Fin.snoc_castSucc]

theorem measurable_clockParentCoordinates {W : ℕ} (p : PathData W) (old : Fin p.C)
    (P : Po) : Measurable (clockParentCoordinates p old P) := by
  apply measurable_pi_iff.mpr
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [clockParentCoordinates,Fin.snoc_last] using
      measurable_clockParentSignal 1 p old P
  · simpa only [clockParentCoordinates,Fin.snoc_castSucc,Function.comp_def] using
      (PiLp.continuous_apply 2 _ i).measurable.comp (measurable_unshearedPacketBase p old)

theorem measurable_clockParentCode {W : ℕ} (p : PathData W) (old : Fin p.C)
    (P : Po) (mesh : ℝ) : Measurable (clockParentCode p old P mesh) := by
  apply measurable_pi_iff.mpr
  intro j
  exact Int.measurable_floor.comp (((measurable_pi_apply j).comp
    (measurable_clockParentCoordinates p old P)).div_const mesh)

theorem clockParentCode_coarse_neighbors {W : ℕ} (p : PathData W) (old : Fin p.C)
    (P : Po) {mesh coarse : ℝ} (hmesh : 0 < mesh) (hsmall : mesh≤coarse)
    {x y : Ev} (hxy : clockParentCode p old P mesh x=clockParentCode p old P mesh y) :
    clockParentCode p old P coarse x∈integerCodeBox 1 (clockParentCode p old P coarse y) :=
  rectangular_coarse_neighbors _ _ (fun _ => mesh) (fun _ => hmesh) (fun _ => hsmall) hxy

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem Native.PathData.Valid.assignedClockCode_eq_original (old : Fin p.C) {P : Po}
    (hP : P.totalDegree≤2) (mesh : ℝ) (z : (hp.frozenPacket old).AssignedLine × ℝ) :
    hp.assignedClockCode old P mesh z = clockParentCode p old P mesh
      ((hp.frozenPacket old).originalIncidence z) := by
  change (fun j => ⌊hp.assignedClockCurve old P z.1 z.2 j/mesh⌋)=_
  rw [hp.assignedClockCurve_eq_original old hP]
  rfl

end Path
end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
