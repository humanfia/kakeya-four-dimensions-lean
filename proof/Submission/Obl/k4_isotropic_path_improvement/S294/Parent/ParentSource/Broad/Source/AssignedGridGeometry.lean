-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AssignedGridGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AssignedGridGeometry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/AssignedGridGeometry.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalCoarseDuration
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.HeightScale
import Submission.Obl.k4_mk_grid_transfer.Grid

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open SourceGeometry Broad.Velocity
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

theorem anisotropic_point_mem_latticeCell {baseMesh hidden : ℝ}
    (hp : 0 < baseMesh) (hb : 0 < hidden) (x : EuclideanSpace ℝ (Fin 4)) :
    baseMesh⁻¹ • heightScale (baseMesh / hidden) x ∈
      latticeCell (fun j => ⌊x j / (if j = 3 then hidden else baseMesh)⌋) := by
  have hcoord (j : Fin 4) : (baseMesh⁻¹ • heightScale (baseMesh / hidden) x) j =
      x j / (if j = 3 then hidden else baseMesh) := by
    change baseMesh⁻¹ * (if j = 3 then baseMesh / hidden * x j else x j) = _
    split_ifs <;> field_simp
  simp only [latticeCell, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Ico]
  intro j
  rw [hcoord]
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

theorem time_window_of_floor_code {coarse t : ℝ} (hH : 0 < coarse) (c : ℤ)
    (hc : ⌊t / coarse⌋ = c) : |t - coarse * ((c : ℝ) + 1 / 2)| ≤ coarse := by
  have hlo := Int.floor_le (t / coarse)
  have hhi := Int.lt_floor_add_one (t / coarse)
  rw [hc] at hlo hhi
  have htlo := (le_div_iff₀ hH).mp hlo
  have hthi := (div_lt_iff₀ hH).mp hhi
  apply abs_le.mpr
  constructor <;> nlinarith

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → MeasureTheory.Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

def Native.PathData.Valid.assignedFineCode (old : Fin p.C) (baseMesh hidden : ℝ) :
    (hp.frozenPacket old).AssignedLine × ℝ → Fin 4 → ℤ :=
  p.originalPhysicalCode Nk old baseMesh hidden ∘ (hp.frozenPacket old).originalIncidence

include hp

theorem Native.PathData.Valid.measurable_assignedFineCode (old : Fin p.C)
    (baseMesh hidden : ℝ) : Measurable (hp.assignedFineCode old baseMesh hidden) :=
  (p.measurable_originalPhysicalCode Nk old baseMesh hidden).comp
    (hp.frozenPacket old).measurable_originalIncidence

theorem Native.PathData.Valid.assigned_fine_lattice_incidence (old : Fin p.C)
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (z : (hp.frozenPacket old).AssignedLine × ℝ) :
    baseMesh⁻¹ • heightScale (baseMesh / hidden)
        (nativePhysicalCurve (normalizedPacketTest Nk p old)
          (normalizedPacketPosition p old z.1) (normalizedPacketVelocity p old z.1) z.2) ∈
      latticeCell (p.originalPhysicalCode Nk old baseMesh hidden
        ((hp.frozenPacket old).originalIncidence z)) := by
  rw [hp.assigned_physical_code]
  exact anisotropic_point_mem_latticeCell hbase hhidden _

theorem Native.PathData.Valid.assigned_coarse_time_window (old : Fin p.C)
    {coarse : ℝ} (hH : 0 < coarse) (c : Fin 4 → ℤ)
    (z : (hp.frozenPacket old).AssignedLine × ℝ)
    (hc : hp.assignedCoarseCode old coarse z = c) :
    |z.2 - coarse * ((c 0 : ℝ) + 1 / 2)| ≤ coarse := by
  have hh := congrFun hc 0
  dsimp [Native.PathData.Valid.assignedCoarseCode, nativeCoarseCode, nativePhysicalCurve,
    normalizedPacketPosition, normalizedPacketVelocity, liftedVector, xp] at hh
  exact time_window_of_floor_code hH (c 0) (by simpa only [mul_one, zero_add] using hh)

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
