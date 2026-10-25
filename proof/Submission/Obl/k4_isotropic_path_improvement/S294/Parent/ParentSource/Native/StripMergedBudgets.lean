-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMergedBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMergedBudgets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMergedBudgets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMergedBudgets.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMergedBudgets.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPowerBudgets

/-! Polynomial output counts can absorb a fixed-power heavy net. The actual
frame and observation slack need only dominate the path envelope. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Submission.Obl.k4_native_finite_terminal_atlas_lift

theorem strip_merged_format_power_budget {N count Hs : ℝ} (hN : 2 ≤ N)
    (M V F : ℕ) (hcount : count ≤ N ^ V) (hHs : Hs ≤ N ^ F) :
    2 * N ^ M + 2 * count + 2 + Hs ≤ N ^ (M + V + F + 3) := by
  have hN1 : 1 ≤ N := by linarith
  have h1 : 1 ≤ N ^ (M + V + F) := one_le_pow₀ hN1
  have hM : N ^ M ≤ N ^ (M + V + F) := pow_le_pow_right₀ hN1 (by omega)
  have hV : N ^ V ≤ N ^ (M + V + F) := pow_le_pow_right₀ hN1 (by omega)
  have hF : N ^ F ≤ N ^ (M + V + F) := pow_le_pow_right₀ hN1 (by omega)
  calc
    _ ≤ 7 * N ^ (M + V + F) := by linarith
    _ ≤ _ := power_absorbs_constant hN (M + V + F) 3 (by norm_num)

theorem strip_merged_card_power_budget {N E count Z r : ℝ} (hN : 2 ≤ N)
    (hE : 1 ≤ E) (hEN : E ≤ N) (hcount0 : 0 ≤ count)
    (M U V : ℕ) (hcount : count ≤ N ^ V)
    (hZ : 0 ≤ Z) (hr : 0 < r) (hZr : Z * r ≤ 2 * E) (hrinv : r⁻¹ ≤ N ^ U) :
    N ^ M * (count * (2 * Z + 1)) ≤ N ^ (M + V + U + 4) := by
  have hE0 : 0 ≤ E := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hU : 1 ≤ N ^ U := one_le_pow₀ hN1
  have hZ' : Z ≤ 2 * E * N ^ U := by
    calc
      _ ≤ (2 * E) / r := (le_div_iff₀ hr).mpr hZr
      _ ≤ _ := by rw [div_eq_mul_inv]; gcongr
  have hZlist : 2 * Z + 1 ≤ 5 * E * N ^ U := by
    nlinarith [mul_le_mul hE hU (by norm_num) hE0]
  calc
    _ ≤ N ^ M * ((N ^ V) * (5 * E * N ^ U)) := by gcongr
    _ ≤ N ^ M * ((N ^ V) * (5 * N * N ^ U)) := by gcongr
    _ = 5 * N ^ (M + V + U + 1) := by simp only [pow_add, pow_one]; ring
    _ ≤ _ := by
      simpa only [show M + V + U + 1 + 3 = M + V + U + 4 by omega] using
        power_absorbs_constant hN (M + V + U + 1) 3 (by norm_num : (5 : ℝ) ≤ 2 ^ 3)

theorem strip_merged_list_envelope {E count C : ℝ} (hE : 1 ≤ E)
    (hcount : count ≤ 3 * E ^ 3) (hC : C ≤ 5 * E) (hC0 : 0 ≤ C) :
    count * (2 * C + 1) ≤ 33 * E ^ 4 := by
  have hE0 : 0 ≤ E := by linarith
  have hC' : 2 * C + 1 ≤ 11 * E := by linarith
  calc
    _ ≤ (3 * E ^ 3) * (11 * E) :=
      mul_le_mul hcount hC' (by linarith) (by positivity)
    _ = _ := by ring

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
