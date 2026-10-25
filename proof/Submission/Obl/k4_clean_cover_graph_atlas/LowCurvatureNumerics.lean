-- Adapted from this LOT tree o173/x0598, commit b7284666,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/LowCurvatureNumerics.lean (namespace renamed).

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Submission.Obl.k4_clean_cover_graph_atlas

/-- The low-curvature cutoff leaves a fixed margin below the square of the
normalized regular derivative scale. -/
theorem low_curvature_error_budget {A a_fit q : ℝ} (hA : 2 ≤ A)
    (hsmall : |q / 2| * a_fit ≤ A ^ (-20 : ℝ)) :
    2 * |q| * (a_fit * A) ≤ (A ^ (-1 : ℝ)) ^ 2 / 2 := by
  have hApos : 0 < A := by linarith
  have hAone : 1 ≤ A := by linarith
  have htail : A ^ (-17 : ℝ) ≤ 1 / 8 := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hAone (by norm_num : (-17 : ℝ) ≤ -3)
    have h2 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2) hA
      (by norm_num : (-3 : ℝ) ≤ 0)
    norm_num at h2
    exact h1.trans (by simpa only [Real.rpow_neg hApos.le, Real.rpow_ofNat] using h2)
  have hpow : A ^ (-20 : ℝ) * A = A ^ (-19 : ℝ) := by
    calc
      _ = A ^ (-20 : ℝ) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hApos]; norm_num
  have hpow' : A ^ (-17 : ℝ) * A ^ (-2 : ℝ) = A ^ (-19 : ℝ) := by
    rw [← Real.rpow_add hApos]
    norm_num
  have hsq : (A ^ (-1 : ℝ)) ^ 2 = A ^ (-2 : ℝ) := by
    simp only [Real.rpow_neg hApos.le, Real.rpow_one, Real.rpow_ofNat, inv_pow]
  have hq : |q| * a_fit ≤ 2 * A ^ (-20 : ℝ) := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsmall
    nlinarith
  calc
    _ = (2 * (|q| * a_fit)) * A := by ring
    _ ≤ (4 * A ^ (-20 : ℝ)) * A := mul_le_mul_of_nonneg_right (by linarith) hApos.le
    _ = 4 * A ^ (-19 : ℝ) := by rw [mul_assoc, hpow]
    _ = (4 * A ^ (-17 : ℝ)) * A ^ (-2 : ℝ) := by rw [mul_assoc, hpow']
    _ ≤ (1 / 2) * A ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hApos.le _)
    _ = _ := by rw [hsq]; ring


end Submission.Obl.k4_clean_cover_graph_atlas
