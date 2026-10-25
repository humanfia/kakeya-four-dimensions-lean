/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Dyadic.lean. Earlier source attributions are retained below.
-/

import Mathlib
import Submission.Obl.k4_matching_homogeneous_records.Encoding

/-!
# Native dyadic widths and their refinement counts
-/

namespace Submission.Obl.k4_native_grid_profile_extension

open Set Filter
open scoped Topology

noncomputable def depthIndex (N r : ℝ) : ℕ := ⌊r * Real.log N / Real.log 2⌋₊

noncomputable def dyadicWidth (N r : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

theorem depthExpression_nonneg {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) :
    0 ≤ r * Real.log N / Real.log 2 :=
  div_nonneg (mul_nonneg hr (Real.log_nonneg hN)) (Real.log_nonneg (by norm_num))

theorem depthIndex_mono {N r s : ℝ} (hN : 1 ≤ N) (hrs : r ≤ s) :
    depthIndex N r ≤ depthIndex N s := by
  apply Nat.floor_le_floor
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hrs (Real.log_nonneg hN))
    (Real.log_nonneg (by norm_num))

theorem dyadicWidth_pos (N r : ℝ) : 0 < dyadicWidth N r := by
  unfold dyadicWidth
  positivity

theorem dyadicWidth_eq_inv_pow {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) :
    dyadicWidth N r = ((2 : ℝ) ^ depthIndex N r)⁻¹ := by
  unfold dyadicWidth depthIndex
  rw [← Int.natCast_floor_eq_floor (depthExpression_nonneg hN hr), zpow_neg,
    zpow_natCast]

theorem floor_div_dyadicWidth {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) (x : ℝ) :
    ⌊x / dyadicWidth N r⌋ = ⌊x * (2 : ℝ) ^ depthIndex N r⌋ := by
  rw [dyadicWidth_eq_inv_pow hN hr, div_inv_eq_mul]

theorem floor_dyadicWidth_refinement {N r s : ℝ} (hN : 1 ≤ N)
    (hr : 0 ≤ r) (hrs : r ≤ s) (x : ℝ) :
    ⌊x / dyadicWidth N r⌋ =
      ⌊x / dyadicWidth N s⌋ / (2 : ℤ) ^ (depthIndex N s - depthIndex N r) := by
  rw [floor_div_dyadicWidth hN hr,
    floor_div_dyadicWidth hN (hr.trans hrs)]
  exact Submission.Obl.k4_matching_homogeneous_records.floor_dyadic_refinement
    (depthIndex_mono hN hrs) x

theorem dyadic_refinement_count_le {N r s : ℝ} (hN : 1 ≤ N)
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    (2 : ℝ) ^ (depthIndex N s - depthIndex N r) ≤ 2 * N ^ (s - r) := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNr : 0 ≤ r * Real.log N / Real.log 2 := depthExpression_nonneg hN hr
  have hNs : 0 ≤ s * Real.log N / Real.log 2 :=
    depthExpression_nonneg hN (hr.trans hrs)
  have hi : depthIndex N r ≤ depthIndex N s := depthIndex_mono hN hrs
  have hlow := Nat.lt_floor_add_one (R := ℝ) (r * Real.log N / Real.log 2)
  have hhigh := Nat.floor_le hNs
  have hexp : ((depthIndex N s - depthIndex N r : ℕ) : ℝ) ≤
      (s - r) * Real.log N / Real.log 2 + 1 := by
    rw [Nat.cast_sub hi]
    dsimp [depthIndex]
    rw [sub_mul, sub_div]
    linarith
  calc
    (2 : ℝ) ^ (depthIndex N s - depthIndex N r) =
        (2 : ℝ) ^ ((depthIndex N s - depthIndex N r : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ ((s - r) * Real.log N / Real.log 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = 2 * N ^ (s - r) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, mul_comm]
      congr 1
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        Real.rpow_def_of_pos (by linarith : 0 < N)]
      congr 1
      field_simp [hlog₂.ne']

end Submission.Obl.k4_native_grid_profile_extension
