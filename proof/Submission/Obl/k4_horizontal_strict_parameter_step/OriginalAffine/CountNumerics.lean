/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/CountNumerics.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.MeshChoice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr

namespace Submission.Obl.k4_horizontal_strict_parameter_step

/-- The original fourth-power witness volume cancels a common-box mass
bound exactly, leaving the desired scalar width count. -/
lemma original_child_band_ratio {K q a w d : ℝ} (hK : 0 < K) (hq : 0 < q)
    (ha : 0 < a) (hw : 0 < w) (C : ℝ) :
    (C * q ^ 4 * a ^ d) / (q ^ 4 * (w * a) ^ d / K ^ 3) = C * K ^ 3 * w ^ (-d) := by
  have ha' : a ^ d ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  have hw' : w ^ d ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hw _)
  rw [Real.mul_rpow hw.le ha.le, Real.rpow_neg hw.le]
  field_simp

/-- The common contact box at slack K squared still gives a pure scalar
width count with a fixed polynomial slack loss. -/
lemma original_common_box_count_ratio {K q a w d : ℝ} (hK : 1 ≤ K) (hq : 0 < q)
    (ha : 0 < a) (hw : 0 < w) :
    (64 * (2 * K + 7) * (K * a ^ d) * (q / 2) * (8 * K ^ 2 * q) *
      (32 * K ^ 4 * q ^ 2)) / (q ^ 4 * (w * a) ^ d / K ^ 3) ≤
      73728 * K ^ 11 * w ^ (-d) := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have heq : 64 * (2 * K + 7) * (K * a ^ d) * (q / 2) * (8 * K ^ 2 * q) *
      (32 * K ^ 4 * q ^ 2) = (8192 * (2 * K + 7) * K ^ 7) * q ^ 4 * a ^ d := by ring
  rw [heq, original_child_band_ratio hKp hq ha hw]
  calc
    _ ≤ (8192 * (9 * K) * K ^ 7) * K ^ 3 * w ^ (-d) := by
      gcongr
      linarith
    _ = _ := by ring

end Submission.Obl.k4_horizontal_strict_parameter_step
