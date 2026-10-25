-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- An original strip of auxiliary gain `h` costs only `N^(hL)` in the
relative-row upper bound. Positive fit and mass losses make this bound
smaller. All constants are absorbed by the displayed exponent gap. -/
theorem no_candidate_row_power_budget
    (N K α β h L fitLoss : ℝ) (hN : 1 ≤ N) (hK : 0 ≤ K)
    (hKpow : K ≤ N ^ α) (hfit : 0 ≤ fitLoss)
    (htwo : 2 ≤ N ^ (β - α - h * L)) :
    2 * K / (N ^ fitLoss * N ^ (-h * L)) ≤ N ^ β := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : 1 ≤ N ^ fitLoss := Real.one_le_rpow hN hfit
  calc
    _ ≤ (2 * N ^ α) / (1 * N ^ (-h * L)) :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity)
        (mul_le_mul_of_nonneg_right hpow (by positivity))
    _ = 2 * N ^ (α + h * L) := by
      rw [one_mul, show -h * L = -(h * L) by ring,
        Real.rpow_neg hNpos.le, div_inv_eq_mul, Real.rpow_add hNpos]
      ring
    _ ≤ N ^ (β - α - h * L) * N ^ (α + h * L) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = N ^ β := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring

/-- The common geometric budget `16H^4` remains subpower after taking a
fixed factor five in the native slack exponent. -/
theorem geometric_row_power_budget
    (N H δ : ℝ) (hN : 1 ≤ N) (hH : 0 ≤ H)
    (hHpow : H ≤ N ^ δ) (hsixteen : 16 ≤ N ^ δ) :
    16 * H ^ 4 ≤ N ^ (5 * δ) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ N ^ δ * (N ^ δ) ^ 4 := by gcongr
    _ = N ^ (5 * δ) := by
      rw [← Real.rpow_mul_natCast hNpos.le δ 4, ← Real.rpow_add hNpos]
      congr 1
      norm_num
      ring

/-- The parent minor-direction absorption uses only the cumulative
area exponent and three powers of the chosen common geometric slack. -/
theorem cumulative_area_power_budget
    (N q H β χ area : ℝ) (hN : 1 ≤ N) (hH : 0 < H)
    (hHpow : H ≤ N ^ β) (htwo : 2 ≤ N ^ (χ - 3 * β))
    (harea : area ≤ q ^ 2 * N ^ (-χ)) :
    area ≤ q ^ 2 / (2 * H ^ 3) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hprod : 2 * H ^ 3 ≤ N ^ χ := by
    calc
      _ ≤ N ^ (χ - 3 * β) * (N ^ β) ^ 3 := by gcongr
      _ = N ^ χ := by
        rw [← Real.rpow_mul_natCast hNpos.le β 3, ← Real.rpow_add hNpos]
        congr 1
        norm_num
        ring
  have hinv : N ^ (-χ) ≤ (2 * H ^ 3)⁻¹ := by
    rw [Real.rpow_neg hNpos.le]
    exact inv_anti₀ (by positivity) hprod
  apply harea.trans
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (sq_nonneg q)

end

end Submission.Obl.k4_finite_affine_parent_sources
