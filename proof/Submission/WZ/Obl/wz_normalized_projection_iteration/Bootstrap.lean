-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Bootstrap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Base

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

/-- Iterating any fixed affine gain brings the exponent arbitrarily close to its fixed point. -/
theorem estimate_of_affine_gain {b q ε : ℝ} (hb : b < 2) (hbε : b < ε)
    (hq0 : 0 < q) (hq1 : q < 1) (hbase : Estimate 2)
    (hstep : ∀ a : ℝ, b < a → a ≤ 2 → Estimate a → Estimate (b + q * (a - b))) :
    Estimate ε := by
  have hden : 0 < 2 - b := sub_pos.mpr hb
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (sub_pos.mpr hbε) hden) hq1
  have hit : ∀ j : ℕ, Estimate (b + (2 - b) * q ^ j) := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      have hlo : b < b + (2 - b) * q ^ j := by
        have hp : 0 < (2 - b) * q ^ j := mul_pos hden (pow_pos hq0 j)
        linarith
      have hhi : b + (2 - b) * q ^ j ≤ 2 := by
        have hp : q ^ j ≤ 1 := pow_le_one₀ hq0.le hq1.le
        nlinarith [pow_nonneg hq0.le j]
      have hs := hstep _ hlo hhi ih
      convert hs using 1
      rw [pow_succ]
      ring
  apply estimate_mono (ε := b + (2 - b) * q ^ N) _ (hit N)
  have hm := (lt_div_iff₀ hden).mp hN
  nlinarith

end WangZahlLot.Obl.wz_normalized_projection_iteration
