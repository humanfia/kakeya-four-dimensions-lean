import Mathlib

open Filter Asymptotics

namespace Submission.Obl.k4_dk4_smoothed_problem

/-- Fixed polynomial losses in the dyadic exponent are subpower in the scale. -/
theorem eventually_poly_le_dyadic_rpow (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, C * ((k : ℝ) + 1) ^ d ≤ ((2 : ℝ) ^ k) ^ ε := by
  have hbase : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have hsmall := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d hbase).const_mul_left
    (C * 2 ^ d)
  filter_upwards [hsmall.bound (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop 1]
    with k hk hk1
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hpoly : C * ((k : ℝ) + 1) ^ d ≤ (C * 2 ^ d) * (k : ℝ) ^ d := by
    calc
      C * ((k : ℝ) + 1) ^ d ≤ C * (2 * (k : ℝ)) ^ d := by
        gcongr
        linarith
      _ = (C * 2 ^ d) * (k : ℝ) ^ d := by rw [mul_pow]; ring
  have hnorm : (C * 2 ^ d) * (k : ℝ) ^ d ≤ ((2 : ℝ) ^ ε) ^ k := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (C * 2 ^ d) * (k : ℝ) ^ d), abs_of_pos (by positivity :
      0 < ((2 : ℝ) ^ ε) ^ k), one_mul] using hk
  exact hpoly.trans (hnorm.trans_eq (Real.rpow_pow_comm (by norm_num) ε k))

theorem tendsto_scales_of_ge (κ : ℕ → ℕ) (hκ : ∀ j, j ≤ κ j) :
    Tendsto (fun j => (2 : ℝ) ^ (κ j)) atTop atTop := by
  have ht : Tendsto κ atTop atTop := tendsto_atTop_mono hκ tendsto_id
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp ht

theorem poly_subpower_on_scales (κ : ℕ → ℕ) (hκ : ∀ j, j ≤ κ j)
    (C : ℝ) (hC : 0 ≤ C) (d : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      C * ((κ j : ℝ) + 1) ^ d ≤ ((2 : ℝ) ^ (κ j)) ^ ε := by
  intro ε hε
  have ht : Tendsto κ atTop atTop := tendsto_atTop_mono hκ tendsto_id
  exact ht.eventually (eventually_poly_le_dyadic_rpow C hC d hε)

theorem poly_subpower_of_tendsto {κ : ℕ → ℕ} (hκ : Tendsto κ atTop atTop)
    (C : ℝ) (hC : 0 ≤ C) (d : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      C * ((κ j : ℝ) + 1) ^ d ≤ ((2 : ℝ) ^ (κ j)) ^ ε := by
  intro ε hε
  exact hκ.eventually (eventually_poly_le_dyadic_rpow C hC d hε)

end Submission.Obl.k4_dk4_smoothed_problem
