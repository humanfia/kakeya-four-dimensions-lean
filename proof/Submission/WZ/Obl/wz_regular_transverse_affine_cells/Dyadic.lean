-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.Dyadic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

/-- A finite dyadic scale just above a given positive radius. -/
lemma exists_dyadic_bottom {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K : ℕ, a ≤ (1 / 2 : ℝ) ^ K ∧ (1 / 2 : ℝ) ^ K < 2 * a := by
  obtain ⟨K, hK, hK'⟩ := exists_nat_pow_near (x := 1 / a) (y := (2 : ℝ))
    (by rw [le_div_iff₀ ha]; simpa using ha1) (by norm_num)
  refine ⟨K, ?_, ?_⟩
  · rw [one_div_pow, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ ha] at hK
    linarith
  · rw [one_div_pow, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ ha, pow_succ] at hK'
    nlinarith

/-- Rounding any radius above the bottom scale uses only the same finite scale range. -/
lemma exists_dyadic_between {a r : ℝ} {K : ℕ} (ha : 0 < a)
    (hK : (1 / 2 : ℝ) ^ K < 2 * a) (har : a ≤ r) (hr1 : r ≤ 1) :
    ∃ k : ℕ, k ≤ K ∧ r ≤ (1 / 2 : ℝ) ^ k ∧ (1 / 2 : ℝ) ^ k < 2 * r := by
  obtain ⟨m, hm, hm'⟩ := exists_dyadic_bottom (ha.trans_le har) hr1
  refine ⟨min m K, min_le_right _ _, ?_, ?_⟩
  · exact hm.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (min_le_left _ _))
  · rcases le_total m K with h | h
    · rwa [min_eq_left h]
    · rw [min_eq_right h]
      linarith

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
