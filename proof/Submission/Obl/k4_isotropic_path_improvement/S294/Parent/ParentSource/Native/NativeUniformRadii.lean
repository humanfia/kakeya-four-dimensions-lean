-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeUniformRadii, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeUniformRadii.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeUniformRadii.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeUniformRadii.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripUniformSecondScaleNet
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeRadiusPowers
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path
import Submission.Obl.k4_profile_density_bounds.Common

/-! The uniform two-scale estimates meet the actual native angular scale
condition at both net stages. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

theorem StripSecondScaleBounds.native_angular_radii {N E κ u a v τ loss : ℝ}
    (h : StripSecondScaleBounds N E 3 u a v τ loss 3 4)
    (hu : 0 ≤ u) (hκ : 1 ≤ κ) (hκE : κ ≤ E) (hEpower : E ≤ N ^ (u / 32)) :
    let r₀ := 3 * N ^ (-u)
    let r₁ := N ^ (-u / 2)
    let r₂ := N ^ (-u / 4)
    let width := r₀ + (1 + 2 * κ) * r₁
    let Rcap := N ^ (-u / 16) / E
    4 * width ≤ r₂ ∧
      32 * (1 + 2 * κ) * r₀ / r₁ ≤ Rcap ∧
      32 * (1 + 2 * κ) * width / r₂ ≤ Rcap ∧
      κ * Rcap ≤ δ N (u / 16) := by
  have hN : 1 ≤ N := by linarith [h.N_two]
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hEpos : 0 < E := zero_lt_one.trans_le h.E_one
  obtain ⟨hr₁, hr₂, _, _, _, hsmall, hpacking, _, hoverlap⟩ := h.scales
  have hwidth : 3 * N ^ (-u) + (1 + 2 * κ) * N ^ (-u / 2) ≤
      3 * N ^ (-u) + (1 + 2 * E) * N ^ (-u / 2) := by gcongr
  have hpack : 32 * (1 + 2 * κ) * (3 * N ^ (-u)) / N ^ (-u / 2) ≤ N ^ (-u / 4) := by
    calc
      _ ≤ 32 * (1 + 2 * E) * (3 * N ^ (-u)) / N ^ (-u / 2) := by gcongr
      _ ≤ _ := hpacking
  have hover : E * (32 * (1 + 2 * κ) *
      (3 * N ^ (-u) + (1 + 2 * κ) * N ^ (-u / 2)) / N ^ (-u / 4)) ≤ N ^ (-u / 16) := by
    calc
      _ ≤ E * (32 * (1 + 2 * E) *
          (3 * N ^ (-u) + (1 + 2 * E) * N ^ (-u / 2)) / N ^ (-u / 4)) := by gcongr
      _ ≤ _ := hoverlap
  dsimp only
  refine ⟨(mul_le_mul_of_nonneg_left hwidth (by norm_num)).trans hsmall,
    native_radius_div_envelope hEpos (native_packing_angular_radius hN hu hEpower (by positivity) hpack),
    native_radius_div_envelope hEpos hover, ?_⟩
  exact (native_angular_scale_of_envelope hEpos hκE (Real.rpow_nonneg hNpos.le _)).trans
    (by simpa only [neg_div, δ, Submission.Obl.k4_profile_density_bounds.width] using
      (Submission.Obl.k4_profile_density_bounds.width_bounds hNpos (u / 16)).1)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
