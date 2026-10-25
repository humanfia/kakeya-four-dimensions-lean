-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Budget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

/-- A power at most one uses no more than the original multiplicative loss. -/
lemma rpow_loss {D X Y p : ℝ} (hD : 1 ≤ D) (hX : 0 < X) (hY : 0 < Y)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (A : ℕ) (h : X ≤ D ^ A * Y) :
    X ^ p / D ^ A ≤ Y ^ p := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hDA : 1 ≤ D ^ A := one_le_pow₀ hD
  have hh := Real.rpow_le_rpow hX.le h hp
  rw [Real.mul_rpow (by positivity) hY.le] at hh
  have hpw : (D ^ A) ^ p ≤ D ^ A := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hDA hp1
  apply (div_le_iff₀ (pow_pos hDpos A)).mpr
  nlinarith only [hh, mul_le_mul_of_nonneg_right hpw (Real.rpow_nonneg hY.le p)]

lemma rpow_negative_loss {D p : ℝ} (hD : 1 ≤ D) (hp : -1 ≤ p) :
    1 / D ≤ D ^ p := by
  have hh := Real.rpow_le_rpow_of_exponent_le hD hp
  simpa only [Real.rpow_neg_one, one_div] using hh

lemma rpow_nat_negative_loss {D p : ℝ} (hD : 1 ≤ D) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A : ℕ) : 1 / D ^ A ≤ (D ^ A) ^ (-p) := by
  exact rpow_negative_loss (one_le_pow₀ hD) (by linarith)

lemma min_middle_loss {D a b p : ℝ} (hD : 4 ≤ D) (ha : 0 < a) (hb : 0 < b)
    (hb8 : b ≤ 8) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (a * b) ^ p / D ≤ (a * min b 2) ^ p := by
  have hmin : b / 4 ≤ min b 2 := le_min (by linarith) (by linarith)
  have hminpos : 0 < min b 2 := lt_min hb (by norm_num)
  have hh : a * b ≤ D ^ (1 : ℕ) * (a * min b 2) := by
    have hmult := mul_le_mul_of_nonneg_right hD (mul_pos ha hminpos).le
    nlinarith only [mul_le_mul_of_nonneg_left hmin ha.le, hmult]
  simpa only [pow_one] using rpow_loss (by linarith : 1 ≤ D) (mul_pos ha hb)
    (mul_pos ha hminpos) hp hp1 1 hh

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
