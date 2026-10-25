-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.CoreRetentionNumerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/CoreRetentionNumerics.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/CoreRetentionNumerics.lean.
All earlier source attributions below are retained. -/
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open scoped ENNReal

/-- Forty value-floor powers and the earlier raw-core floors pay the
complete original loss before any later physical-state selection. -/
theorem original_value_core_loss_bound {K : ℝ} (hK : 2 ≤ K) (R : ℕ) :
    ENNReal.ofReal (K ^ 10) * ENNReal.ofReal ((K ^ 40)⁻¹) +
      ENNReal.ofReal (K ^ 10) * ENNReal.ofReal (2 * K ^ (3 * R + 18)) *
        ENNReal.ofReal ((K ^ (3 * R + 58))⁻¹) ≤ ENNReal.ofReal ((K ^ 20)⁻¹) := by
  have hKpos : 0 < K := by linarith
  have hKzero : 0 ≤ K := hKpos.le
  have hpower : K ^ (3 * R + 58) = K ^ (3 * R + 18) * K ^ 40 := by
    rw [← pow_add]
  have hid : K ^ 10 * (K ^ 40)⁻¹ +
      K ^ 10 * (2 * K ^ (3 * R + 18)) * (K ^ (3 * R + 58))⁻¹ = 3 / K ^ 30 := by
    rw [hpower]
    field_simp [pow_ne_zero _ hKpos.ne']
    ring
  have hten : 3 ≤ K ^ 10 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hK 10
    norm_num at hh
    linarith
  have hmul : 3 * K ^ 20 ≤ K ^ 30 := by
    rw [show (30 : ℕ) = 20 + 10 by norm_num, pow_add]
    calc
      3 * K ^ 20 = K ^ 20 * 3 := mul_comm _ _
      _ ≤ K ^ 20 * K ^ 10 := mul_le_mul_of_nonneg_left hten (pow_nonneg hKzero 20)
  have hreal : K ^ 10 * (K ^ 40)⁻¹ +
      K ^ 10 * (2 * K ^ (3 * R + 18)) * (K ^ (3 * R + 58))⁻¹ ≤ (K ^ 20)⁻¹ := by
    rw [hid, ← one_div]
    exact (div_le_div_iff₀ (pow_pos hKpos 30) (pow_pos hKpos 20)).mpr (by simpa only [one_mul] using hmul)
  calc
    _ = ENNReal.ofReal (K ^ 10 * (K ^ 40)⁻¹ +
        K ^ 10 * (2 * K ^ (3 * R + 18)) * (K ^ (3 * R + 58))⁻¹) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

theorem original_core_loss_small {K κ : ℝ} (hκ : 1 ≤ κ) (hK : 2304 ≤ K)
    (hκK : 3 * κ ≤ K) : (K ^ 20)⁻¹ ≤ κ⁻¹ / 1024 := by
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  have hKone : 1 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hsq : 2304 * K ≤ K ^ 2 := by nlinarith
  have h20 : 1024 * κ ≤ K ^ 20 := by
    have hh : K ^ 2 ≤ K ^ 20 := pow_le_pow_right₀ hKone (by norm_num)
    nlinarith
  have hh := one_div_le_one_div_of_le (show 0 < 1024 * κ by positivity) h20
  simpa only [one_div, div_eq_mul_inv, mul_inv_rev, one_mul] using hh

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
