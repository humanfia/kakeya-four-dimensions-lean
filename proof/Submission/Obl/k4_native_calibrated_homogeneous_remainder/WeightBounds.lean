import Submission.Obl.k4_tempered_grid_selection.Exponents

/-! Clipping world-weight exponents before selecting a common limiting class. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open Submission.Obl.k4_tempered_grid_selection

/-- Zero and very small weights receive a bounded exponent. -/
noncomputable def weightExponent (C N a : ℝ) : ℝ :=
  if 0 < a then boundedExponent C N a else C

theorem abs_weightExponent_le (C N a : ℝ) (hC : 0 ≤ C) :
    |weightExponent C N a| ≤ C := by
  unfold weightExponent
  split_ifs
  · exact abs_boundedExponent _ _ _ hC
  · rw [abs_of_nonneg hC]

/-- A probability weight has a nonnegative logarithmic exponent. -/
theorem logarithmicExponent_nonneg {N a : ℝ} (hN : 1 < N) (ha : 0 < a) (ha1 : a ≤ 1) :
    0 ≤ logarithmicExponent N a :=
  div_nonneg (neg_nonneg.mpr (Real.log_nonpos ha.le ha1)) (Real.log_pos hN).le

/-- Clipping only enlarges the upper bound on a probability weight. -/
theorem weight_le_rpow_neg_weightExponent {C N a : ℝ}
    (hC : 0 ≤ C) (hN : 1 < N) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    a ≤ N ^ (-weightExponent C N a) := by
  by_cases ha0 : 0 < a
  · have hnonneg := logarithmicExponent_nonneg hN ha0 ha1
    have hclip : boundedExponent C N a ≤ logarithmicExponent N a :=
      max_le (by linarith) (min_le_right _ _)
    calc
      a = N ^ (-logarithmicExponent N a) := (rpow_neg_logarithmicExponent hN ha0).symm
      _ ≤ N ^ (-boundedExponent C N a) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (neg_le_neg hclip)
      _ = N ^ (-weightExponent C N a) := by rw [weightExponent, ite_eq_left ha0]
  · have : a = 0 := le_antisymm (le_of_not_gt ha0) ha
    rw [this]
    positivity

/-- A selected weight exponent below the clipping threshold is the actual
logarithmic exponent, and its weight is strictly positive. -/
theorem weightExponent_unclipped {C N a : ℝ}
    (hC : 0 ≤ C) (hN : 1 < N) (ha1 : a ≤ 1)
    (hclip : weightExponent C N a < C) :
    0 < a ∧ weightExponent C N a = logarithmicExponent N a := by
  have ha : 0 < a := by
    by_contra hn
    simp only [weightExponent, ite_eq_right hn] at hclip
    exact (lt_irrefl C) hclip
  have hnonneg := logarithmicExponent_nonneg hN ha ha1
  have hlt : logarithmicExponent N a < C := by
    by_contra hn
    have hge : C ≤ logarithmicExponent N a := le_of_not_gt hn
    simp only [weightExponent, ite_eq_left ha, boundedExponent, min_eq_left hge] at hclip
    exact (not_lt_of_ge (le_max_right _ _)) hclip
  refine ⟨ha, ?_⟩
  simp only [weightExponent, ite_eq_left ha, boundedExponent, min_eq_right hlt.le,
    max_eq_right (by linarith : -C ≤ logarithmicExponent N a)]

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
