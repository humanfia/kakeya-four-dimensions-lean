-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeDeepScale, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeDeepScale.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeDeepScale.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeDeepScale.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeTimeRatio

/-! A fixed original lookahead resolves any required base mesh once the
source envelope exponent is chosen small enough. The frame and original
path scale errors are charged explicitly. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

theorem native_deep_base_scale_bound {N κ κ₁ sOld sFine δ₀ L σ slack meshExponent : ℝ}
    {Told Tfine : ℕ} (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hδL : 0 ≤ δ₀ * L)
    (hOld : (2 : ℝ) ^ Told ≤ N ^ ((κ₁ * sOld + δ₀) * L))
    (hFine : N ^ ((κ₁ * sFine - δ₀) * L) ≤ (2 : ℝ) ^ Tfine)
    (hκpower : κ ≤ N ^ σ) (hfour : 4 ≤ N ^ slack)
    (hgap : meshExponent + 3 * σ + slack + 4 * δ₀ * L ≤ κ₁ * (sFine - sOld) * L) :
    (1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ) * ((2 : ℝ) ^ Told / (2 : ℝ) ^ Tfine) ≤
      N ^ (-meshExponent) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hκpos : 0 ≤ κ := zero_le_one.trans hκ
  have hNfactor : 1 ≤ N ^ (2 * δ₀ * L) := Real.one_le_rpow hN (by nlinarith)
  have hκcube : κ ≤ κ ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hκ (by norm_num : (1 : ℕ) ≤ 3)
  have hframe : κ ≤ κ ^ 3 * N ^ (2 * δ₀ * L) := hκcube.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hNfactor (pow_nonneg hκpos 3))
  have hcoefficient : 1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ ≤
      4 * κ ^ 3 * N ^ (2 * δ₀ * L) := by nlinarith
  have hratio := native_time_ratio_of_scale_bounds hNpos hOld hFine
  have hκbound : 4 * κ ^ 3 ≤ N ^ slack * (N ^ σ) ^ 3 :=
    mul_le_mul hfour (pow_le_pow_left₀ hκpos hκpower 3) (by positivity) (by positivity)
  calc
    _ ≤ (4 * κ ^ 3 * N ^ (2 * δ₀ * L)) * ((2 : ℝ) ^ Told / (2 : ℝ) ^ Tfine) :=
      mul_le_mul_of_nonneg_right hcoefficient (by positivity)
    _ = (4 * κ ^ 3) * (N ^ (2 * δ₀ * L) * ((2 : ℝ) ^ Told / (2 : ℝ) ^ Tfine)) := by ring
    _ ≤ (N ^ slack * (N ^ σ) ^ 3) * N ^ ((-κ₁ * (sFine - sOld) + 4 * δ₀) * L) :=
      mul_le_mul hκbound hratio (by positivity) (by positivity)
    _ = N ^ (slack + 3 * σ + (-κ₁ * (sFine - sOld) + 4 * δ₀) * L) := by
      rw [← Real.rpow_mul_natCast hNpos.le σ 3, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
