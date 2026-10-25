-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.BootstrapConstants.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

theorem bootstrap_base_bounds {C K c : ℝ} (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    1 ≤ C * K / c ∧ K ≤ C * K / c ∧ C / c ≤ C * K / c := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hCK : K ≤ C * K := by nlinarith
  have hKbase : K ≤ C * K / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc1 hK0]
  refine ⟨hK.trans hKbase, hKbase, ?_⟩
  exact div_le_div_of_nonneg_right (by nlinarith) hc.le

/-- A single bootstrap step fits an explicit exponential recurrence for its
counting constant. The exceptional fraction is allowed to increase. -/
theorem bootstrap_constant_step {B C c e M : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hc : 0 < c) (hce : c ≤ e) (hM : 1 ≤ M) (hCB : C / c ≤ B) (n : ℕ) :
    (C * B ^ ((2 * M) ^ n) / e) ^ M ≤ B ^ ((2 * M) ^ (n + 1)) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have he : 0 < e := hc.trans_le hce
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hA : 1 ≤ (2 * M) ^ n := one_le_pow₀ (by linarith)
  have hbase : C * B ^ ((2 * M) ^ n) / e ≤ B ^ (2 * (2 * M) ^ n) := by
    calc C * B ^ ((2 * M) ^ n) / e ≤ C * B ^ ((2 * M) ^ n) / c :=
        div_le_div_of_nonneg_left (by positivity) hc hce
      _ = (C / c) * B ^ ((2 * M) ^ n) := by ring
      _ ≤ B * B ^ ((2 * M) ^ n) := mul_le_mul_of_nonneg_right hCB (by positivity)
      _ = B ^ (1 + (2 * M) ^ n) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hB), Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB (by linarith)
  calc (C * B ^ ((2 * M) ^ n) / e) ^ M ≤ (B ^ (2 * (2 * M) ^ n)) ^ M :=
      Real.rpow_le_rpow (by positivity) hbase hM0
    _ = B ^ ((2 * M) ^ (n + 1)) := by
      rw [← Real.rpow_mul hB0, pow_succ]
      congr 1
      ring

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
