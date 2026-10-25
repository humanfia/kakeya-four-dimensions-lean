-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.QuarterCoreGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/QuarterCoreGeometry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/QuarterCoreGeometry.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/QuarterCoreGeometry.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/QuarterCoreGeometry.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.GoodBaseCenters

/-! # Good quarter-core centers in the actual local power coordinates -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

/-- A power mesh two exponents finer than the analytic branch radius
places every original good point in a quarter core. -/
theorem power_mesh_in_quarter_core {K : ℝ} (hK : 2 ≤ K) (R : ℕ)
    {z c : EuclideanSpace ℝ (Fin 3)} (hmesh : ‖z - c‖ ≤ (K ^ (R + 2))⁻¹) :
    ‖(K ^ R) • (z - c)‖ ≤ 1 / 4 := by
  have hKp : 0 < K := by linarith
  have hK2 : (4 : ℝ) ≤ K ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hK 2
    norm_num at hh
    exact hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hKp R)]
  calc
    _ ≤ K ^ R * (K ^ (R + 2))⁻¹ := mul_le_mul_of_nonneg_left hmesh (by positivity)
    _ = (K ^ 2)⁻¹ := by rw [pow_add]; field_simp
    _ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hK2
    _ = 1 / 4 := by norm_num

/-- Reconstruction in the ORIGINAL base coordinates is exact. -/
theorem power_chart_reconstruction {K : ℝ} (hK : 0 < K) (R : ℕ)
    (z c : EuclideanSpace ℝ (Fin 3)) :
    c + (K ^ R)⁻¹ • ((K ^ R) • (z - c)) = z := by
  rw [smul_smul, inv_mul_cancel₀ (pow_pos hK R).ne', one_smul]
  abel

/-- Quarter cores cover the entire original good set with centers still
IN that good set, at one uniformly bounded power cost. -/
theorem original_good_quarter_centers_power
    (R : ℕ) {K : ℝ} (hK : 2 ≤ K)
    (A : Set (EuclideanSpace ℝ (Fin 3)))
    (hA : ∀ z ∈ A, ∀ j, |z j| ≤ 1) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 3)),
      (S.card : ℝ) ≤ K ^ (3 * R + 18) ∧
      (∀ c ∈ S, c ∈ A) ∧
      ∀ z ∈ A, ∃ c ∈ S, ‖(K ^ R) • (z - c)‖ ≤ 1 / 4 := by
  obtain ⟨S, hcard, hsub, hcover⟩ := original_good_base_centers_power (R + 2) hK A hA
  refine ⟨S, ?_, hsub, ?_⟩
  · convert hcard using 1
  · intro z hz
    obtain ⟨c, hc, hnear⟩ := hcover z hz
    exact ⟨c, hc, power_mesh_in_quarter_core hK R hnear⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
