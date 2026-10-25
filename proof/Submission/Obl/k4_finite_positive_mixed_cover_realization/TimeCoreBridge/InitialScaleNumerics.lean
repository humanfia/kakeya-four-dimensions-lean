-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/InitialScaleNumerics.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o173/x0598, commit b7284666,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/InitialScaleNumerics.lean (namespace renamed).

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

/-- Uniform polynomial budgets for the physical initial scale. The high-curvature
cutoff bounds its reciprocal even if the original quadratic coefficient is tiny. -/
theorem initial_scale_bounds (flat : Bool) {A B a_fit q d : ℝ}
    (hA : 2 ≤ A) (hB : 0 < B) (ha_fit : a_fit ≤ 1)
    (hclass : flat = false ↔ |q / 2| * a_fit ≤ A ^ (-20 : ℝ))
    (hlo : 4 * A ^ (-1 : ℝ) ≤ |d|) (hhi : |d| ≤ A) :
    let s := if flat then B ^ 2 * |q| else B * |d|
    0 < s ∧ s ≤ B * A + B ^ 2 * |q| ∧ s⁻¹ ≤ A / B + A ^ (20 : ℕ) / B ^ 2 := by
  have hApos : 0 < A := by linarith
  cases flat
  · change 0 < B * |d| ∧ _
    have hlower : B / A ≤ B * |d| := by
      rw [Real.rpow_neg_one] at hlo
      have hh := mul_le_mul_of_nonneg_left hlo hB.le
      rw [div_eq_mul_inv]
      nlinarith [mul_pos hB (inv_pos.mpr hApos)]
    have hs : 0 < B * |d| := (div_pos hB hApos).trans_le hlower
    have hinv : (B * |d|)⁻¹ ≤ A / B := by
      have hh := one_div_le_one_div_of_le (div_pos hB hApos) hlower
      simpa only [one_div, inv_div] using hh
    refine ⟨hs, ?_, hinv.trans (le_add_of_nonneg_right (by positivity))⟩
    exact (mul_le_mul_of_nonneg_left hhi hB.le).trans (le_add_of_nonneg_right (by positivity))
  · change 0 < B ^ 2 * |q| ∧ _
    have hlarge : A ^ (-20 : ℝ) < |q / 2| * a_fit := by
      have hh : ¬ |q / 2| * a_fit ≤ A ^ (-20 : ℝ) := by
        intro hh
        have he := hclass.mpr hh
        cases he
      exact lt_of_not_ge hh
    have hq : A ^ (-20 : ℝ) ≤ |q| := by
      have hh := mul_le_mul_of_nonneg_left ha_fit (abs_nonneg (q / 2))
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hlarge hh
      nlinarith [Real.rpow_nonneg hApos.le (-20 : ℝ), abs_nonneg q]
    have hlower : B ^ 2 * A ^ (-20 : ℝ) ≤ B ^ 2 * |q| :=
      mul_le_mul_of_nonneg_left hq (sq_nonneg B)
    have hfloor : 0 < B ^ 2 * A ^ (-20 : ℝ) := by positivity
    have hinv : (B ^ 2 * |q|)⁻¹ ≤ A ^ (20 : ℕ) / B ^ 2 := by
      have hh := one_div_le_one_div_of_le hfloor hlower
      have he : (B ^ 2 * A ^ (-20 : ℝ))⁻¹ = A ^ (20 : ℕ) / B ^ 2 := by
        rw [mul_inv_rev, Real.rpow_neg hApos.le, Real.rpow_ofNat, inv_inv]
        ring
      simpa only [one_div, he] using hh
    exact ⟨hfloor.trans_le hlower, le_add_of_nonneg_left (by positivity),
      hinv.trans (le_add_of_nonneg_left (by positivity))⟩


end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
