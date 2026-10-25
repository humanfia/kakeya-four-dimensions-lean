/- Adapted from this LOT tree, obligation o119, session x0404, commit b1aa67e,
   Submission/Obl/k4_finite_width_critical_contradiction/CompDyadic.lean. -/
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompDecode
import Submission.Obl.k4_joint_homogenization

/-!
# Dyadic thicknesses and the single-world observation of o075

`dl N r = 2 ^ (-⌊r log N / log 2⌋)` is the thickness at depth `r`.  When `ρ₀ log₂ N` is an
integer, `dl N (ρ₀ + s) = dl N ρ₀ * dl N s`, so the o075 observation at depth `ρ₀ + s`
of an encoded incidence is a world observation at depth `s`.
-/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp

attribute [local simp] encCoeff_zero encCoeff_one encCoeff_two encCoeff_three encCoeff_four encCoeff_five

open MeasureTheory Set

/-- The dyadic thickness at depth `r` for base `N`. -/
noncomputable def dl (N r : ℝ) : ℝ := (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

theorem dl_pos (N r : ℝ) : 0 < dl N r := zpow_pos (by norm_num) _

theorem dl_add_of_int {N ρ₀ : ℝ} (j : ℤ) (hj : ρ₀ * (Real.log N / Real.log 2) = j) (s : ℝ) :
    dl N (ρ₀ + s) = dl N ρ₀ * dl N s := by
  unfold dl
  have h1 : (ρ₀ + s) * Real.log N / Real.log 2 = s * Real.log N / Real.log 2 + j := by
    rw [← hj]; ring
  have h2 : ρ₀ * Real.log N / Real.log 2 = (j : ℝ) := by rw [← hj]; ring
  rw [h1, h2, Int.floor_add_intCast, Int.floor_intCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

theorem dl_le_one {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) : dl N r ≤ 1 := by
  unfold dl
  apply zpow_le_one_of_nonpos₀ (by norm_num)
  have : 0 ≤ r * Real.log N / Real.log 2 :=
    div_nonneg (mul_nonneg hr (Real.log_nonneg hN)) (Real.log_nonneg (by norm_num))
  have : 0 ≤ ⌊r * Real.log N / Real.log 2⌋ := Int.floor_nonneg.mpr this
  omega

/-- The reciprocal thickness is an integer power of two for nonnegative depth. -/
theorem dl_inv_eq_two_pow {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) :
    ∃ m : ℕ, (dl N r)⁻¹ = (2 : ℝ) ^ m := by
  have hnn : 0 ≤ ⌊r * Real.log N / Real.log 2⌋ :=
    Int.floor_nonneg.mpr (div_nonneg (mul_nonneg hr (Real.log_nonneg hN))
      (Real.log_nonneg (by norm_num)))
  refine ⟨⌊r * Real.log N / Real.log 2⌋.toNat, ?_⟩
  unfold dl
  rw [zpow_neg, inv_inv, ← zpow_natCast, Int.toNat_of_nonneg hnn]

/-- The o075 observation is the joint observation with hidden scale one. -/
theorem observation075_eq (n r u : ℝ) :
    Submission.Obl.k4_joint_homogenization.Observation n r u = jobs 1 (dl n r) (dl n u) := by
  funext p
  simp only [Submission.Obl.k4_joint_homogenization.Observation, jobs, dl, one_mul]

theorem two_rpow_log_div (N x : ℝ) (hN : 0 < N) :
    (2 : ℝ) ^ (x * Real.log N / Real.log 2) = N ^ x := by
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hN]
  congr 1
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- `dl N r ≥ N ^ (-r)`. -/
theorem rpow_neg_le_dl {N r : ℝ} (hN : 0 < N) : N ^ (-r) ≤ dl N r := by
  unfold dl
  rw [← Real.rpow_intCast, ← two_rpow_log_div N (-r) hN]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  have := Int.floor_le (r * Real.log N / Real.log 2)
  have h : -r * Real.log N / Real.log 2 = -(r * Real.log N / Real.log 2) := by ring
  linarith

/-- `dl N r ≤ 2 N ^ (-r)`. -/
theorem dl_le_two_mul_rpow {N r : ℝ} (hN : 0 < N) : dl N r ≤ 2 * N ^ (-r) := by
  unfold dl
  rw [← Real.rpow_intCast, ← two_rpow_log_div N (-r) hN]
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (-r * Real.log N / Real.log 2) =
      (2 : ℝ) ^ (-r * Real.log N / Real.log 2 + 1) := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  rw [h2]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  have := Int.lt_floor_add_one (r * Real.log N / Real.log 2)
  have h : -r * Real.log N / Real.log 2 = -(r * Real.log N / Real.log 2) := by ring
  linarith

theorem dl_inv_le_rpow {N r : ℝ} (hN : 0 < N) : (dl N r)⁻¹ ≤ N ^ r := by
  have h := rpow_neg_le_dl (r := r) hN
  rw [Real.rpow_neg hN.le] at h
  have hpos : 0 < N ^ r := Real.rpow_pos_of_pos hN r
  calc (dl N r)⁻¹ ≤ ((N ^ r)⁻¹)⁻¹ := inv_anti₀ (by positivity) h
    _ = N ^ r := inv_inv _

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Comp
