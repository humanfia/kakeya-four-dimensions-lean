-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace Submission.Obl.k4_finite_affine_parent_sources

open scoped ENNReal

theorem original_angular_reference_ratio {N : ℝ} (hN : 0 < N)
    (fL S r eG ePure eShare eParent : ℝ) :
    (ENNReal.ofReal (N ^ (-eParent)))⁻¹ *
      ((ENNReal.ofReal (N ^ (-fL - S * r + eG)) /
        ENNReal.ofReal (N ^ (-fL - ePure))) /
          ENNReal.ofReal (N ^ (-eShare))) =
      ENNReal.ofReal (N ^ (-S * r + eG + ePure + eShare + eParent)) := by
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hN _),
    ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hN _),
    ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hN _),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg hN.le _))]
  congr 1
  rw [← Real.rpow_neg hN.le, ← Real.rpow_sub hN, ← Real.rpow_sub hN,
    ← Real.rpow_add hN]
  congr 1
  ring

theorem original_angular_reference_coefficient {N : ℝ} (hN : 0 < N)
    (H fL S r eG ePure eShare eParent : ℝ) :
    (ENNReal.ofReal (N ^ (-eParent)))⁻¹ *
      (ENNReal.ofReal ((6 * H + 2) ^ 2) *
        ((ENNReal.ofReal (N ^ (-fL - S * r + eG)) /
          ENNReal.ofReal (N ^ (-fL - ePure))) /
            ENNReal.ofReal (N ^ (-eShare)))) =
      ENNReal.ofReal (((6 * H + 2) ^ 2 *
        N ^ (eG + ePure + eShare + eParent)) * N ^ (-S * r)) := by
  rw [mul_left_comm, original_angular_reference_ratio hN,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  have he : -S * r + eG + ePure + eShare + eParent =
      (eG + ePure + eShare + eParent) + (-S * r) := by ring
  rw [he, Real.rpow_add hN]
  ring

/-- A fixed coarse menu loses only its depth mesh in the angular
exponent. The reference normalization and blur costs fit in model K. -/
theorem palette_depth_loss {N : ℝ} (hN : 1 ≤ N)
    {A unit L S v r mesh K : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hdepth : unit * L * v - mesh ≤ r)
    (hbudget : 6 * A * N ^ (S * mesh) ≤ K) :
    6 * (A * N ^ (-S * r)) ≤ K * (N ^ (unit * L)) ^ (-S * v) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ (-S * r) ≤ N ^ (S * mesh) * (N ^ (unit * L)) ^ (-S * v) := by
    rw [← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith [mul_le_mul_of_nonneg_left hdepth hS]
  calc
    _ ≤ 6 * (A * (N ^ (S * mesh) * (N ^ (unit * L)) ^ (-S * v))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hA) (by norm_num)
    _ = (6 * A * N ^ (S * mesh)) * (N ^ (unit * L)) ^ (-S * v) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (by positivity) _)

/-- The quadratic raw-cap loss has a fixed explicit input exponent.
Only its scale threshold depends on the prescribed output exponent. -/
theorem explicit_quadratic_cap_budget (θ : ℝ) (hθ : 0 < θ) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N D : ℝ, N₀ ≤ N → 1 ≤ D →
      D ≤ N ^ (min 1 (θ / 4)) → D ≤ N ∧ 400 * D ^ 2 ≤ N ^ θ := by
  refine ⟨max 2 ((400 : ℝ) ^ (2 / θ)), le_max_left _ _, ?_⟩
  intro N D hN hD hDN
  have hN1 : 1 ≤ N := by linarith [((le_max_left _ _).trans hN : (2 : ℝ) ≤ N)]
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hD0 : 0 ≤ D := by linarith
  have hlarge : 400 ≤ N ^ (θ / 2) := by
    have he : (2 / θ) * (θ / 2) = (1 : ℝ) := by field_simp
    calc
      (400 : ℝ) = ((400 : ℝ) ^ (2 / θ)) ^ (θ / 2) := by
        rw [← Real.rpow_mul (by norm_num), he, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _)
        ((le_max_right _ _).trans hN) (by positivity)
  have hDpow : D ^ 2 ≤ N ^ (θ / 2) := by
    calc
      D ^ 2 ≤ (N ^ (min 1 (θ / 4))) ^ 2 := pow_le_pow_left₀ hD0 hDN 2
      _ = N ^ ((min 1 (θ / 4)) * 2) := (Real.rpow_mul_natCast hN0.le _ 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by
        linarith [min_le_right (1 : ℝ) (θ / 4)])
  refine ⟨?_, ?_⟩
  · calc
      D ≤ N ^ (min 1 (θ / 4)) := hDN
      _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)
      _ = N := Real.rpow_one _
  · calc
      400 * D ^ 2 ≤ N ^ (θ / 2) * N ^ (θ / 2) :=
        mul_le_mul hlarge hDpow (sq_nonneg _) (Real.rpow_nonneg hN0.le _)
      _ = N ^ θ := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring

/-- A planar code one extra native power finer than all tested bins
leaves room for the full major-axis readout and the palette blur. -/
theorem palette_blur_budget {N β : ℝ} (n : ℕ) (hN : 8 ≤ N) (hβ : β ≤ 1) :
    0 < N ^ (-((n : ℝ) + 2)) ∧
      0 < 4 * N ^ β * N ^ (-((n : ℝ) + 2)) ∧
      2 * (4 * N ^ β * N ^ (-((n : ℝ) + 2))) ≤ N ^ (-(n : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hH : N ^ β ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hβ
  refine ⟨by positivity, by positivity, ?_⟩
  calc
    _ = (8 * N ^ β) * N ^ (-((n : ℝ) + 2)) := by ring
    _ ≤ (N * N) * N ^ (-((n : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hN hH (Real.rpow_nonneg hN0.le _) hN0.le) (by positivity)
    _ = N ^ (2 + (-((n : ℝ) + 2))) := by
      rw [Real.rpow_add hN0, Real.rpow_two, pow_two]
    _ = N ^ (-(n : ℝ)) := by congr 1; ring

/-- The actual parent's angular cover has only a quadratic slack cost.
The axis threshold affects the code mesh, rather than this coefficient. -/
theorem palette_parent_budget {N κ S mesh e : ℝ} (hN : 1 ≤ N) (hκ : 1 ≤ κ)
    (hS : S ≤ 1) (hmesh : 0 ≤ mesh) :
    6 * ((6 * (6 * κ) + 2) ^ 2 * N ^ e) * N ^ (S * mesh) ≤
      10000 * κ ^ 2 * N ^ (e + mesh) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hc : 6 * (6 * (6 * κ) + 2) ^ 2 ≤ 10000 * κ ^ 2 := by
    nlinarith [sq_nonneg (κ - 1)]
  have hp : N ^ (S * mesh) ≤ N ^ mesh :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  calc
    _ = (6 * (6 * (6 * κ) + 2) ^ 2) * (N ^ e * N ^ (S * mesh)) := by ring
    _ ≤ (10000 * κ ^ 2) * (N ^ e * N ^ mesh) :=
      mul_le_mul hc (mul_le_mul_of_nonneg_left hp (by positivity))
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hN0]

end Submission.Obl.k4_finite_affine_parent_sources
