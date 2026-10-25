-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.SupportGap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/SupportGap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/SupportGap.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 5bf2ec7212f0;
-- source Submission/Obl/k4_isotropic_path_improvement/SupportGap.lean.
-- The support and duration scales are separated here.
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

noncomputable section

/-- The fine base mesh cancels from the anisotropic determinant estimate.
Only the hidden support deficit remains. -/
theorem anisotropic_incidence_mass_power_bound
    {X V M cells C K p b H d θ : ℝ}
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hK : 0 < K)
    (hp : 0 < p) (hb : 0 < b) (hH : 0 < H)
    (hbudget : (p / b / 256) * θ * (X / (K * p)) ^ 4 ≤ cells * C ^ 3 * V ^ 4)
    (hprior : V ≤ K * M / H)
    (hcount : cells ≤ K * (H / p) ^ 3 * (H / b) ^ d) :
    θ * X ^ 4 ≤ 256 * C ^ 3 * K ^ 9 * M ^ 4 * (b / H) ^ (1 - d) := by
  have hVpow := pow_le_pow_left₀ hV hprior 4
  have hupper : cells * C ^ 3 * V ^ 4 ≤
      (K * (H / p) ^ 3 * (H / b) ^ d) * C ^ 3 * (K * M / H) ^ 4 := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hcount (pow_nonneg hC 3)
    · exact hVpow
    · exact pow_nonneg hV 4
    · positivity
  have hscaled := mul_le_mul_of_nonneg_right (hbudget.trans hupper)
    (show 0 ≤ (256 * b / p) * (K * p) ^ 4 by positivity)
  have hcancel : (p / b / 256) * θ * (X / (K * p)) ^ 4 *
      ((256 * b / p) * (K * p) ^ 4) = θ * X ^ 4 := by field_simp
  rw [hcancel] at hscaled
  have hr : 0 < H / b := div_pos hH hb
  have hinv : b / H = (H / b) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, inv_div]
  have hpower : (H / b) ^ d * (b / H) = (b / H) ^ (1 - d) := by
    rw [hinv, ← Real.rpow_add hr, ← Real.rpow_mul hr.le]
    congr 1
    ring
  refine hscaled.trans_eq ?_
  calc
    _ = 256 * C ^ 3 * K ^ 9 * M ^ 4 * ((H / b) ^ d * (b / H)) := by field_simp
    _ = _ := by rw [hpower]

theorem anisotropic_incidence_mass_power_bound_two_thirds
    {X V M cells C K p b d θ : ℝ}
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hK : 0 < K) (hp : 0 < p) (hb : 0 < b)
    (hbudget : (p / b / 256) * θ * (X / (K * p)) ^ 4 ≤ cells * C ^ 3 * V ^ 4)
    (hprior : V ≤ K * M / b ^ ((2 : ℝ) / 3))
    (hcount : cells ≤ K * (b ^ ((2 : ℝ) / 3) / p) ^ 3 *
      (b ^ ((2 : ℝ) / 3) / b) ^ d) :
    θ * X ^ 4 ≤ 256 * C ^ 3 * K ^ 9 * M ^ 4 * b ^ ((1 - d) / 3) := by
  have h := anisotropic_incidence_mass_power_bound hV hC hK hp hb
    (Real.rpow_pos_of_pos hb _) hbudget hprior hcount
  have hratio : b / b ^ ((2 : ℝ) / 3) = b ^ ((1 : ℝ) / 3) := by
    have h' := Real.rpow_sub hb (1 : ℝ) ((2 : ℝ) / 3)
    norm_num at h'
    exact h'.symm
  rw [hratio, ← Real.rpow_mul hb.le] at h
  simpa only [show (1 / 3 : ℝ) * (1 - d) = (1 - d) / 3 by ring] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
