-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.PhysicalCellNeighbors, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/PhysicalCellNeighbors.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/PhysicalCellNeighbors.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalCodePruning
import Submission.Obl.k4_scalar_grid_cartesian_field.RectangularCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open Submission.Lib.K4ListedExceptions

/-- A rectangular fine cell meeting a coarse cube lies in its neighboring cubes.
The grids need not be nested. -/
theorem rectangular_coarse_neighbors {n : ℕ} (x y width : Fin n → ℝ)
    {coarse : ℝ} (hwidth : ∀ j, 0 < width j) (hsmall : ∀ j, width j ≤ coarse)
    (heq : (fun j => (⌊x j / width j⌋ : ℤ)) = fun j => ⌊y j / width j⌋) :
    (fun j => (⌊x j / coarse⌋ : ℤ)) ∈
      integerCodeBox 1 (fun j => ⌊y j / coarse⌋) := by
  apply floor_code_mem_integerCodeBox 1 x y (fun _ => coarse)
    (fun j => (hwidth j).trans_le (hsmall j))
  intro j
  simpa only [Nat.cast_one, one_mul] using
    (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq (hwidth j) (congrFun heq j)).le.trans
      (hsmall j)

theorem Native.PathData.originalPhysicalCode_coarse_neighbors {W : ℕ}
    (p : Native.PathData W) (Nk : ℝ) (old : Fin p.C) {baseMesh hidden coarse : ℝ}
    (hp : 0 < baseMesh) (hb : 0 < hidden) (hpH : baseMesh ≤ coarse) (hbH : hidden ≤ coarse)
    {x y : Ev}
    (hxy : p.originalPhysicalCode Nk old baseMesh hidden x =
      p.originalPhysicalCode Nk old baseMesh hidden y) :
    p.originalPhysicalCode Nk old coarse coarse x ∈
      integerCodeBox 1 (p.originalPhysicalCode Nk old coarse coarse y) := by
  rw [p.originalPhysicalCode_coordinates, p.originalPhysicalCode_coordinates] at hxy
  rw [p.originalPhysicalCode_isotropic, p.originalPhysicalCode_isotropic]
  exact rectangular_coarse_neighbors _ _ (fun j => if j = 3 then hidden else baseMesh)
    (fun j => by split_ifs <;> assumption) (fun j => by split_ifs <;> assumption) hxy

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
