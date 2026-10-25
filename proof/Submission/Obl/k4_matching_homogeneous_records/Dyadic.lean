import Submission.Obl.k4_matching_homogeneous_records.Radius

namespace Submission.Obl.k4_matching_homogeneous_records

noncomputable def dyadicHeight (N : ℝ) (r : ℝ) : ℕ :=
  ⌈Real.logb 2 (N ^ r)⌉₊

lemma dyadicHeight_mono {N : ℝ} (hN : 1 ≤ N) : Monotone (dyadicHeight N) := by
  intro a b hab
  apply Nat.ceil_mono
  exact Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_le_rpow_of_exponent_le hN hab)

lemma dyadicHeight_bounds {N r : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) :
    N ^ r ≤ (2 : ℝ) ^ dyadicHeight N r ∧
    (2 : ℝ) ^ dyadicHeight N r ≤ 2 * N ^ r := by
  have hx : 0 < N ^ r := Real.rpow_pos_of_pos (by linarith) _
  have hl : 0 ≤ Real.logb 2 (N ^ r) :=
    Real.logb_nonneg (by norm_num) (Real.one_le_rpow hN hr)
  constructor
  · rw [← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (by norm_num) hx).1 (Nat.le_ceil _)
  · have hc := (Nat.ceil_lt_add_one hl).le
    have hh := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hc
    rw [Real.rpow_natCast, Real.rpow_add (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hx, Real.rpow_one] at hh
    simpa [dyadicHeight, mul_comm] using hh

noncomputable def dyadicCenter (h : ℕ) (t : ℝ) : ℝ :=
  ((Int.floor (t * (2 : ℝ) ^ h) : ℝ) + 1 / 2) / (2 : ℝ) ^ h

lemma dyadicCenter_mem {h : ℕ} {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    dyadicCenter h t ∈ Set.Icc (0 : ℝ) 1 := by
  have hp : 0 < (2 : ℝ) ^ h := by positivity
  have hi : 0 ≤ Int.floor (t * (2 : ℝ) ^ h) := Int.floor_nonneg.mpr (mul_nonneg ht.1 hp.le)
  have hj : Int.floor (t * (2 : ℝ) ^ h) < (2 : ℤ) ^ h := by
    apply Int.floor_lt.mpr
    push_cast
    nlinarith [ht.2]
  have hj' : (Int.floor (t * (2 : ℝ) ^ h) : ℝ) + 1 ≤ (2 : ℝ) ^ h := by
    exact_mod_cast hj
  constructor
  · exact div_nonneg (by positivity) hp.le
  · apply (div_le_one hp).2
    linarith

lemma dyadicCenter_dist (h : ℕ) (t : ℝ) :
    |dyadicCenter h t - t| ≤ ((2 : ℝ) ^ h)⁻¹ := by
  have hp : 0 < (2 : ℝ) ^ h := by positivity
  have hl := Int.floor_le (t * (2 : ℝ) ^ h)
  have hu := Int.lt_floor_add_one (t * (2 : ℝ) ^ h)
  have he : dyadicCenter h t - t =
      ((Int.floor (t * (2 : ℝ) ^ h) : ℝ) + 1 / 2 - t * (2 : ℝ) ^ h) / (2 : ℝ) ^ h := by
    rw [dyadicCenter]
    field_simp
  rw [he, abs_div, abs_of_pos hp, inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ hp.le
  apply abs_le.mpr
  constructor <;> linarith

end Submission.Obl.k4_matching_homogeneous_records
