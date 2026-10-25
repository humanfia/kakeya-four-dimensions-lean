-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.NativeCubeCurvature, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/NativeCubeCurvature.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/NativeCubeCurvature.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCubeCurvature.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCubeCurvature.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCube

/-! Native curvature and the uniform small-value-bin cutoff. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open MvPolynomial Set
open k4_quadratic_atlas_normalization

noncomputable section

/-- An actual second-derivative bound at one original point controls the
constant hidden curvature of the normalized quadratic everywhere. -/
theorem nativeCubeTest_curvature_bound {κ B a : ℝ}
    (hκ : 0 < κ) (hB : 0 < B) (ha : 0 < a) (P : Poly) (hP : P.totalDegree ≤ 2)
    (x : Fin 4 → ℝ)
    (hsecond : |eval x (pderiv 3 (pderiv 3 P))| ≤ κ * (B / a) ^ 2) :
    |curvature (nativeCubeTest κ B a P) 3| ≤ κ := by
  have hid := (nativeCubeTest_derivatives hκ.ne' hB.ne' ha.ne' P x).2
  have hbound : |eval (nativeCubePoint κ B a x)
      (pderiv 3 (pderiv 3 (nativeCubeTest κ B a P)))| ≤ κ := by
    rw [hid, abs_mul, abs_pow, abs_of_pos (div_pos ha hB)]
    have hh := mul_le_mul_of_nonneg_left hsecond (sq_nonneg (a / B))
    convert hh using 1 <;> field_simp
  rw [second_pderiv_eq_curvature _ ((nativeCubeTest_totalDegree _ _ _ _).trans hP) 3,
    eval_C] at hbound
  exact hbound

/-- Sufficiently narrow value bins of a normalized native equation always
lie in the small-curvature case. The cutoff is a fixed power before all
source and format data. -/
theorem native_value_bin_small_curvature {K ε c : ℝ} (hK : 2 ≤ K)
    (hε : 0 < ε) (hεK : ε ≤ (K ^ 6)⁻¹) (hc : |c| ≤ K) :
    |c| ≤ (K ^ 5 * ε)⁻¹ := by
  have hKp : 0 < K := by linarith
  have hh : ε * K ^ 6 ≤ 1 := (le_div_iff₀ (pow_pos hKp 6)).mp
    (by simpa only [one_div] using hεK)
  apply hc.trans
  rw [← one_div]
  apply (le_div_iff₀ (mul_pos (pow_pos hKp 5) hε)).mpr
  convert hh using 1 <;> ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
