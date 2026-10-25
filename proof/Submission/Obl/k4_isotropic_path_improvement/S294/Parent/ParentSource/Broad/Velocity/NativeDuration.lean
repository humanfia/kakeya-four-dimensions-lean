-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.NativeDuration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/NativeDuration.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/NativeDuration.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 5bf2ec7212f0;
-- source Submission/Obl/k4_isotropic_path_improvement/NativeDuration.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.HeightScale
import Submission.Obl.k4_mk_grid_transfer.Grid

/-!
The native trajectory/cube count pays for short-duration deletion over
all physical cubes, with the unchanged original trajectory prior.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity


open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_mk_grid_transfer

noncomputable section


/-- The time coordinate alone gives the per-cell duration ceiling. -/
theorem cell_duration_le (curve : ℝ → Space) (origin : ℝ)
    (K fine : ℝ) (hK : 0 ≤ K) (hfine : 0 < fine) (hfirst : ∀ t, curve t 0 = origin + t)
    (z : Fin 4 → ℤ) (F : ℝ → ℝ≥0∞) (hbound : ∀ t, F t ≤ ENNReal.ofReal K)
    (hcell : ∀ t, F t ≠ 0 → fine⁻¹ • curve t ∈ latticeCell z) :
    (∫⁻ t, F t) ≤ ENNReal.ofReal (K * fine) := by
  let c : ℝ := fine * (z 0 : ℝ) - origin
  have htime (t : ℝ) (ht : F t ≠ 0) : t ∈ Ico c (c + fine) := by
    have hf := Set.mem_univ_pi.mp (hcell t ht) (0 : Fin 4)
    change (z 0 : ℝ) ≤ fine⁻¹ * curve t 0 ∧
      fine⁻¹ * curve t 0 < (z 0 : ℝ) + 1 at hf
    rw [hfirst t] at hf
    have hlo := mul_le_mul_of_nonneg_left hf.1 hfine.le
    have hhi := mul_lt_mul_of_pos_left hf.2 hfine
    simp only [← mul_assoc, mul_inv_cancel₀ hfine.ne', one_mul, mul_one] at hlo hhi
    constructor <;> dsimp [c] <;> linarith
  calc
    _ ≤ ∫⁻ t, (Ico c (c + fine)).indicator (fun _ => ENNReal.ofReal K) t := by
      apply lintegral_mono
      intro t
      by_cases ht : F t = 0
      · rw [ht]
        exact zero_le
      · rw [Set.indicator_of_mem (htime t ht)]
        exact hbound t
    _ = ENNReal.ofReal K * ENNReal.ofReal fine := by
      rw [lintegral_indicator measurableSet_Ico]
      simp only [setLIntegral_const, Real.volume_Ico, add_sub_cancel_left]
    _ = ENNReal.ofReal (K * fine) := (ENNReal.ofReal_mul hK).symm

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
