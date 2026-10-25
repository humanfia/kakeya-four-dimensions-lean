-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripBudget.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripBudget.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripBudget.lean.
   Original comments and attributions are preserved below. -/
import Submission.Lib.K4VelocityStrips
import Submission.Obl.k4_native_finite_terminal_atlas_lift.FrameComposition

/-! Convert the explicit strip-width saving to the frozen determinant target. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

/-- All losses are charged before comparing the strip exponent with the
requested determinant gain. This retains the distinction between those exponents. -/
theorem strip_determinant_power_bound (Q : Matrix (Fin 2) (Fin 2) ℝ) (T : ℕ)
    {N oldWidth error loss u gain K D r : ℝ} {e n : StripSpace}
    (hN : 1 ≤ N) (hK : 0 < K) (hD : 0 ≤ D) (hr : 0 < r)
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0)
    (hprofile : |Q.det| * (4 : ℝ) ^ T ≤ N ^ (-oldWidth + error))
    (hbudget : K * (1 + D) ≤ N ^ loss) (hradius : r ≤ N ^ (-u))
    (hgain : error + loss + gain ≤ u) :
    |Matrix.det (Q * stripLocalFrame K D r e n)| * (4 : ℝ) ^ T ≤
      N ^ (-(oldWidth + gain)) := by
  have hNpos : 0 < N := by linarith
  have hlocal : |Matrix.det (stripLocalFrame K D r e n)| * (4 : ℝ) ^ (0 : ℕ) ≤
      N ^ (-u + loss) := by
    rw [pow_zero, mul_one, stripLocalFrame_abs_det hK hD hr he hn hen]
    calc
      K * (1 + D) * r ≤ N ^ loss * N ^ (-u) :=
        mul_le_mul hbudget hradius hr.le (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (-u + loss) := by rw [← Real.rpow_add hNpos]; congr 1; ring
  have hmul := Submission.Obl.k4_native_finite_terminal_atlas_lift.determinant_time_mul_bound
    (T := T) (U := 0) hNpos hprofile hlocal
  calc
    _ ≤ N ^ (-(oldWidth + u) + (error + loss)) := by simpa only [Nat.add_zero] using hmul
    _ ≤ N ^ (-(oldWidth + gain)) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
