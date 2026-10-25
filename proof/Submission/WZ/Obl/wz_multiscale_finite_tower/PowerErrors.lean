-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.PowerErrors.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Scales

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

lemma power_coefficient_bound {d C c h a : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hha : h ≤ a) (hsmall : C * d ^ h ≤ 1) :
    c * d ^ a ≤ 1 := by
  calc
    _ ≤ c * d ^ h := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hd hd1 hha) hc
    _ ≤ C * d ^ h := mul_le_mul_of_nonneg_right hcC (Real.rpow_nonneg hd.le _)
    _ ≤ 1 := hsmall

lemma inverse_power_error_bound {d C a ε : ℝ} (hd : 0 < d)
    (hsmall : C * d ^ (ε - a) ≤ 1) : C * d ^ (-a) ≤ d ^ (-ε) := by
  calc
    _ = (C * d ^ (ε - a)) * d ^ (-ε) := by
      rw [mul_assoc, ← Real.rpow_add hd]
      congr 2
      ring
    _ ≤ 1 * d ^ (-ε) := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hd.le _)
    _ = _ := one_mul _

lemma density_power_bound {d C a ε : ℝ} (hd : 0 < d) (hC : 0 < C)
    (hsmall : C * d ^ (ε - a) ≤ 1) : d ^ ε ≤ d ^ a / C := by
  apply (le_div_iff₀ hC).mpr
  calc
    d ^ ε * C = (C * d ^ (ε - a)) * d ^ a := by
      rw [mul_assoc, ← Real.rpow_add hd, sub_add_cancel]
      ring
    _ ≤ 1 * d ^ a := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hd.le _)
    _ = _ := one_mul _

end WangZahlLot.Obl.wz_multiscale_finite_tower
