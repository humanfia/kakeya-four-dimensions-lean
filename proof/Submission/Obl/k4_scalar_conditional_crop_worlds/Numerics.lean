import Submission.Obl.k4_scalar_conditional_crop_worlds.Definitions

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

/-- The conditional noisy-box density has a uniform polynomial bound. The scalar change of
variables contributes a factor at most one. -/
lemma crop_density_le {N m u p w : ℝ} (hN : 2 ≤ N) (hu : 0 ≤ u) (A : ℕ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hp : N ^ (-(A : ℝ) - 1) ≤ p) :
    w * (N ^ (-m))⁻¹ ^ 5 * (N ^ (-u)) ^ 2 / p ≤ N ^ (⌈5 * m⌉₊ + A + 1) := by
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hδ : 0 < N ^ (-(A : ℝ) - 1) := Real.rpow_pos_of_pos hNp _
  have hp0 : 0 < p := hδ.trans_le hp
  have ha0 : 0 ≤ N ^ (-u) := Real.rpow_nonneg hNp.le _
  have ha1 : N ^ (-u) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have ha2 : (N ^ (-u)) ^ 2 ≤ 1 := pow_le_one₀ ha0 ha1
  have hwa : w * (N ^ (-u)) ^ 2 ≤ 1 := by
    simpa using mul_le_mul hw1 ha2 (by positivity : 0 ≤ (N ^ (-u)) ^ 2) zero_le_one
  have hσ0 : 0 ≤ (N ^ (-m))⁻¹ ^ 5 := by positivity
  have hc : w * (N ^ (-m))⁻¹ ^ 5 * (N ^ (-u)) ^ 2 ≤ (N ^ (-m))⁻¹ ^ 5 := by
    calc w * (N ^ (-m))⁻¹ ^ 5 * (N ^ (-u)) ^ 2 =
        (N ^ (-m))⁻¹ ^ 5 * (w * (N ^ (-u)) ^ 2) := by ring
      _ ≤ (N ^ (-m))⁻¹ ^ 5 * 1 := mul_le_mul_of_nonneg_left hwa hσ0
      _ = _ := mul_one _
  have hσ : (N ^ (-m))⁻¹ ^ 5 = N ^ (5 * m) := by
    rw [Real.rpow_neg hNp.le, inv_inv, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    congr 1
    ring
  calc w * (N ^ (-m))⁻¹ ^ 5 * (N ^ (-u)) ^ 2 / p ≤ (N ^ (-m))⁻¹ ^ 5 / p :=
      div_le_div_of_nonneg_right hc hp0.le
    _ ≤ (N ^ (-m))⁻¹ ^ 5 / N ^ (-(A : ℝ) - 1) :=
      div_le_div_of_nonneg_left hσ0 hδ hp
    _ = N ^ (5 * m + (A : ℝ) + 1) := by
      rw [hσ, div_eq_mul_inv, ← Real.rpow_neg hNp.le, ← Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ N ^ (⌈5 * m⌉₊ + A + 1) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hN1
      push_cast
      linarith [Nat.le_ceil (5 * m)]

end Submission.Obl.k4_scalar_conditional_crop_worlds
