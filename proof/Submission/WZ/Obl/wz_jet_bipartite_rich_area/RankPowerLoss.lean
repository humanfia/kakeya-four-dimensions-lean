-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.RankPowerLoss.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

/-- Choosing a large logarithmic base makes an exponential rank cost an
arbitrarily small power of the scale ratio. -/
theorem four_pow_floor_logb_le_rpow {B x ε : ℝ}
    (hB : 1 < B) (hx : 1 ≤ x) (hε : 0 ≤ ε) (hbase : 4 ≤ B^ε) :
    (4:ℝ)^⌊Real.logb B x⌋₊ ≤ x^ε := by
  have hB0 : 0 ≤ B := (zero_lt_one.trans hB).le
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hfloor := Nat.floor_le (Real.logb_nonneg hB hx)
  have hpower : B^⌊Real.logb B x⌋₊ ≤ x := by
    rw [← Real.rpow_natCast]
    exact (Real.le_logb_iff_rpow_le hB hx0).mp hfloor
  calc
    _ ≤ (B^ε)^⌊Real.logb B x⌋₊ := pow_le_pow_left₀ (by norm_num) hbase _
    _ = (B^⌊Real.logb B x⌋₊)^ε := by
      rw [← Real.rpow_mul_natCast hB0, mul_comm, Real.rpow_natCast_mul hB0]
    _ ≤ x^ε := Real.rpow_le_rpow (pow_nonneg hB0 _) hpower hε

/-- The exponential pair-rank constant is controlled by a small inverse
power of the resolution, uniformly for windows of length at most one. -/
theorem four_pow_resolution_rank_le {B δ s w ε : ℝ}
    (hB : 1 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδs : δ ≤ s)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hε : 0 ≤ ε) (hbase : 4 ≤ B^ε) :
    (4:ℝ)^(⌊Real.logb B (w/s)⌋₊+2)+1 ≤ 17*δ^(-ε) := by
  have hs : 0 < s := hδ.trans_le hδs
  have hinv : 1 ≤ 1/δ := (one_le_div hδ).mpr hδ1
  have hrank : ⌊Real.logb B (w/s)⌋₊ ≤ ⌊Real.logb B (1/δ)⌋₊ := by
    by_cases hwpos : 0 < w
    · apply Nat.floor_mono
      apply Real.logb_le_logb_of_le hB (div_pos hwpos hs)
      calc
        w/s ≤ 1/s := div_le_div_of_nonneg_right hw1 hs.le
        _ ≤ 1/δ := one_div_le_one_div_of_le hδ hδs
    · have hw0 : w=0 := le_antisymm (le_of_not_gt hwpos) hw
      simp only [hw0, zero_div, Real.logb_zero, Nat.floor_zero]
      exact Nat.zero_le _
  have hp : (4:ℝ)^⌊Real.logb B (w/s)⌋₊ ≤ δ^(-ε) := by
    calc
      _ ≤ (4:ℝ)^⌊Real.logb B (1/δ)⌋₊ := pow_le_pow_right₀ (by norm_num) hrank
      _ ≤ (1/δ)^ε := four_pow_floor_logb_le_rpow hB hinv hε hbase
      _ = δ^(-ε) := by rw [one_div, Real.inv_rpow hδ.le, Real.rpow_neg hδ.le]
  have hone : 1 ≤ δ^(-ε) := by
    have hh := Real.one_le_rpow hinv hε
    simpa only [one_div, Real.inv_rpow hδ.le, Real.rpow_neg hδ.le] using hh
  rw [pow_add]
  norm_num only [pow_two] at *
  nlinarith only [hp, hone]

/-- A suitable base exists for every positive power loss. -/
theorem exists_rank_base (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 1 < B ∧ 4 ≤ B^ε := by
  refine ⟨(4:ℝ)^(1/ε), ?_, ?_⟩
  · exact Real.one_lt_rpow (by norm_num) (div_pos (by norm_num) hε)
  · rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4), one_div_mul_cancel hε.ne', Real.rpow_one]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
