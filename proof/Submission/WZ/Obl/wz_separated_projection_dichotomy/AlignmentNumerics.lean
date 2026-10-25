-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AlignmentNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentBudget

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

theorem AlignmentScaleBudget.transverse_gain {δ ε η κ R : ℝ}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R) (hlower : δ ^ (-κ) ≤ R) :
    (32 * R) ^ (1 - ε) ≤ δ ^ (2 * η) * R / 18 := by
  have hpow : 576 ≤ δ ^ (2 * η) * R ^ ε := by
    calc 576 ≤ δ ^ (2 * η - κ * ε) := hb.transverse_reserve
      _ = δ ^ (2 * η) * (δ ^ (-κ)) ^ ε := by
        rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hlower hε.le) (by positivity)
  have h32 : (32 : ℝ) ^ (1 - ε) ≤ 32 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 32) (by linarith : 1 - ε ≤ 1)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) hR.le]
  calc (32 : ℝ) ^ (1 - ε) * R ^ (1 - ε) ≤ 32 * R ^ (1 - ε) :=
        mul_le_mul_of_nonneg_right h32 (by positivity)
    _ = (576 / 18) * R ^ (1 - ε) := by norm_num
    _ ≤ (δ ^ (2 * η) * R ^ ε / 18) * R ^ (1 - ε) := by
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow (by norm_num)) (by positivity)
    _ = δ ^ (2 * η) * R / 18 := by
      rw [div_mul_eq_mul_div, mul_assoc, ← Real.rpow_add hR]
      simp only [add_sub_cancel, Real.rpow_one]

theorem AlignmentScaleBudget.radial_gain {δ ε η κ R K : ℝ}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hlower : δ ^ (-ε / 2) ≤ R) (hK : 0 ≤ K)
    (hKbound : K ≤ 8192 * δ ^ (-η - κ)) :
    (160 * R) ^ (1 - ε) *
      (8 * K ^ (2 : ℕ) * energyConstant (1 - ε / 2) * (2 / R) ^ (1 - ε / 2)) ≤ δ ^ (2 * η) := by
  have hE : 0 < energyConstant (1 - ε / 2) := energyConstant_pos (by linarith)
  have hconst : 0 ≤ alignmentConstant ε := by unfold alignmentConstant; positivity
  have hRpow : R ^ (-ε / 2) ≤ δ ^ (ε ^ 2 / 4) := by
    calc R ^ (-ε / 2) ≤ (δ ^ (-ε / 2)) ^ (-ε / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlower (by linarith)
      _ = _ := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
  have hid : (160 * R) ^ (1 - ε) *
      (8 * (8192 * δ ^ (-η - κ)) ^ (2 : ℕ) * energyConstant (1 - ε / 2) *
        (2 / R) ^ (1 - ε / 2)) =
      alignmentConstant ε * δ ^ (-2 * η - 2 * κ) * R ^ (-ε / 2) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 160) hR.le,
      Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le, mul_pow,
      ← Real.rpow_mul_natCast hδ.le (-η - κ) 2]
    have hpower : R ^ (1 - ε) / R ^ (1 - ε / 2) = R ^ (-ε / 2) := by
      rw [← Real.rpow_sub hR]
      congr 1
      ring
    have hδpow : δ ^ ((-η - κ) * (2 : ℕ)) = δ ^ (-2 * η - 2 * κ) := by congr 1; norm_num; ring
    rw [hδpow]
    calc _ = alignmentConstant ε * δ ^ (-2 * η - 2 * κ) *
        (R ^ (1 - ε) / R ^ (1 - ε / 2)) := by unfold alignmentConstant; ring
      _ = _ := by rw [hpower]
  calc (160 * R) ^ (1 - ε) *
      (8 * K ^ (2 : ℕ) * energyConstant (1 - ε / 2) * (2 / R) ^ (1 - ε / 2)) ≤
        (160 * R) ^ (1 - ε) *
          (8 * (8192 * δ ^ (-η - κ)) ^ (2 : ℕ) * energyConstant (1 - ε / 2) *
            (2 / R) ^ (1 - ε / 2)) := by gcongr
    _ = alignmentConstant ε * δ ^ (-2 * η - 2 * κ) * R ^ (-ε / 2) := hid
    _ ≤ alignmentConstant ε * δ ^ (-2 * η - 2 * κ) * δ ^ (ε ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hRpow (by positivity)
    _ = alignmentConstant ε * δ ^ (ε ^ 2 / 4 - 2 * η - 2 * κ) := by
      rw [mul_assoc, ← Real.rpow_add hδ]
      congr 1
      congr 1
      ring
    _ ≤ δ ^ (2 * η) := hb.radial_reserve

end WangZahlLot.Obl.wz_separated_projection_dichotomy
