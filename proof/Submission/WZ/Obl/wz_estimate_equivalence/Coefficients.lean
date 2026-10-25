-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_estimate_equivalence.Coefficients.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_estimate_equivalence.Estimates

namespace WangZahlLot.Obl.wz_estimate_equivalence

/-- Separating the two counting constants in the arbitrary-error bound. -/
theorem general_coefficient_eq {σ a q N B m l : ℝ}
    (hm : 0 < m) (hl : 0 ≤ l) (hB : 0 ≤ B) :
    a * q * m⁻¹ * N * (m ^ (-(3 / 2 : ℝ)) * l * B) ^ (-σ) =
      (a * q * N * B ^ (-σ)) * m ^ (-1 + 3 * σ / 2) * l ^ (-σ) := by
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hm.le _) hl) hB,
    Real.mul_rpow (Real.rpow_nonneg hm.le _) hl, ← Real.rpow_mul hm.le]
  have hexp : -(3 / 2 : ℝ) * -σ = 3 * σ / 2 := by ring
  rw [hexp, Real.rpow_add hm, Real.rpow_neg_one]
  ring

/-- In the admissible range of `σ`, larger counting constants weaken the estimate. -/
theorem general_coefficient_le {σ a q N B m l : ℝ}
    (hσ : 0 ≤ σ) (hσmax : σ ≤ 2 / 3) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hN : 0 ≤ N) (hB : 0 ≤ B) (hm : 1 ≤ m) (hl : 1 ≤ l) :
    a * q * m⁻¹ * N * (m ^ (-(3 / 2 : ℝ)) * l * B) ^ (-σ) ≤
      a * q * N * B ^ (-σ) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hl0 : 0 ≤ l := le_trans zero_le_one hl
  rw [general_coefficient_eq hm0 hl0 hB]
  have hmpow : m ^ (-1 + 3 * σ / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm (by linarith)
  have hlpow : l ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hl (neg_nonpos.mpr hσ)
  calc
    (a * q * N * B ^ (-σ)) * m ^ (-1 + 3 * σ / 2) * l ^ (-σ) ≤
        (a * q * N * B ^ (-σ)) * 1 * 1 := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_estimate_equivalence
