-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeRadiusPowers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeRadiusPowers.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeRadiusPowers.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeRadiusPowers.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeScaleNumerics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Radius conversion for applying the original native angular cap to
both stages of the heavy-strip net. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

theorem native_packing_angular_radius {N E u radius : ℝ}
    (hN : 1 ≤ N) (hu : 0 ≤ u) (hE : E ≤ N ^ (u / 32))
    (hradius : 0 ≤ radius) (hbound : radius ≤ N ^ (-u / 4)) :
    E * radius ≤ N ^ (-u / 16) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  calc
    _ ≤ N ^ (u / 32) * N ^ (-u / 4) :=
      mul_le_mul hE hbound hradius (Real.rpow_nonneg hNpos.le _)
    _ = N ^ (u / 32 + (-u / 4)) := (Real.rpow_add hNpos _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem native_radius_div_envelope {E radius bound : ℝ} (hE : 0 < E)
    (hbound : E * radius ≤ bound) : radius ≤ bound / E := by
  exact (le_div_iff₀ hE).mpr (by simpa only [mul_comm] using hbound)

theorem native_angular_scale_of_envelope {κ E power : ℝ}
    (hE : 0 < E) (hκE : κ ≤ E) (hpower : 0 ≤ power) :
    κ * (power / E) ≤ power := by
  calc
    _ ≤ E * (power / E) := mul_le_mul_of_nonneg_right hκE (div_nonneg hpower hE.le)
    _ = power := by field_simp

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
