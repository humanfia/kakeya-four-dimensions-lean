-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.NativeSignal, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/NativeSignal.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/NativeSignal.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 38d075b9;
-- source Submission/Obl/k4_isotropic_path_improvement/NormalizedTrajectoryLegs.lean (native signal declarations only).

import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices


namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SixPath

open Set MvPolynomial

noncomputable section

/-- The actual old quadratic test evaluated along the frozen indexed line. -/
def nativeSignalPolynomial (P : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) :
    Polynomial ℝ :=
  Submission.Obl.k4_quadratic_slope_volume.linePolynomial P
    (WithLp.toLp 2 ![l.2 0, l.2 1, l.2 2])
    (WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5])

theorem eval_nativeSignalPolynomial (P : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (nativeSignalPolynomial P l).eval t =
      eval ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] P := by
  rw [nativeSignalPolynomial, Submission.Obl.k4_quadratic_slope_volume.eval_linePolynomial]
  rfl

theorem degree_nativeSignalPolynomial (P : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (hP : P.totalDegree ≤ 2) :
    (nativeSignalPolynomial P l).natDegree ≤ 2 :=
  (Submission.Obl.k4_quadratic_slope_volume.natDegree_linePolynomial_le _ _ _).trans hP

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SixPath
