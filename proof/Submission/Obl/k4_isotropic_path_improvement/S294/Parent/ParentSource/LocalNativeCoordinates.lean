-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.LocalNativeCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/LocalNativeCoordinates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/LocalNativeCoordinates.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/LocalNativeCoordinates.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/LocalNativeCoordinates.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.AffineTransport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeEquation

/-! # The actual base translation and dilation of a native quadratic -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open MvPolynomial

noncomputable section

/-- Move a good base center to zero and dilate only the base variables.
The hidden native value is left in its original unit. -/
def localNativePolynomial (c : Fin 3 → ℝ) (scale : ℝ) (P : Poly) : Poly :=
  transportPolynomial c (Matrix.diagonal (fun _ => scale)) 1 P

theorem localNativePolynomial_totalDegree (c : Fin 3 → ℝ) (scale : ℝ) (P : Poly) :
    (localNativePolynomial c scale P).totalDegree ≤ P.totalDegree :=
  totalDegree_transportPolynomial_le _ _ _ _

/-- The local polynomial is evaluated at the actual original base point,
including its original hidden coordinate. -/
theorem localNativePolynomial_eval (c : Fin 3 → ℝ) (scale : ℝ) (P : Poly)
    (x : EuclideanSpace ℝ (Fin 3)) (w : ℝ) :
    eval ![x 0, x 1, x 2, w] (localNativePolynomial c scale P) =
      eval (Fin.snoc (fun j => c j + scale * x j) w) P := by
  rw [localNativePolynomial, eval_transportPolynomial]
  apply congrArg (fun z : Fin 4 → ℝ => eval z P)
  funext j
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    change 1 * w = w
    ring
  | cast j =>
    rw [Fin.snoc_castSucc]
    fin_cases j <;> simp [coordinateMap, Matrix.diagonal]

/-- Base localization preserves the actual hidden derivative scale. -/
theorem localNativePolynomial_pderiv (c : Fin 3 → ℝ) (scale : ℝ) (P : Poly) :
    pderiv 3 (localNativePolynomial c scale P) =
      localNativePolynomial c scale (pderiv 3 P) := by
  simp only [localNativePolynomial, pderiv_transportPolynomial, map_one, one_mul]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
