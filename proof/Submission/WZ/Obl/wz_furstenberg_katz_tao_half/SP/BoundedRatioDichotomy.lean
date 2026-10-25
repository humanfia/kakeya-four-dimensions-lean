-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.BoundedRatioDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.RatioDichotomy

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- The escaping ratio may be chosen in the unit interval. This controls
the diameter of the numerator projection in the product sumset. -/
theorem bounded_large_ratio_dichotomy {q h : ℝ} (hq : 0 < q) (A : Finset ℝ)
    (hpair : ∃ c ∈ A, ∃ d ∈ A, q ≤ |c - d|) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ LargeDenominatorRatios q A,
      t ∈ Set.Icc (0 : ℝ) 1 ∧ dist t x ≤ 2 * h) ∨
    ∃ r ∈ LargeDenominatorRatios q A, r ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ b : ℝ, (b = 0 ∨ b = 1) ∧
        ∀ s ∈ LargeDenominatorRatios q A, h < dist ((r + b) / 2) s := by
  classical
  let T := LargeDenominatorRatios q A ∩ Set.Icc (0 : ℝ) 1
  have h01 := LargeDenominatorRatios.zero_one hq hpair
  have hT0 : (0 : ℝ) ∈ T := ⟨h01.1, by constructor <;> norm_num⟩
  have hT1 : (1 : ℝ) ∈ T := ⟨h01.2, by constructor <;> norm_num⟩
  by_cases hdense : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ T, dist t x ≤ 2 * h
  · exact Or.inl (fun x hx => by
      obtain ⟨t, ht, htx⟩ := hdense x hx
      exact ⟨t, ht.1, ht.2, htx⟩)
  · right
    push Not at hdense
    obtain ⟨x, hx, hfar⟩ := hdense
    obtain ⟨r, hr, b, hb, hescape⟩ := exists_half_escape
      ((LargeDenominatorRatios.finite q A).inter_of_left _).isCompact ⟨0, hT0⟩
      ⟨x, hx, fun s hs => by simpa only [dist_comm] using hfar s hs⟩
    refine ⟨r, hr.1, hr.2, b, hb, ?_⟩
    have hy : (r + b) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      rcases hb with rfl | rfl <;> constructor <;> linarith [hr.2.1, hr.2.2]
    intro s hs
    by_cases hs0 : 0 ≤ s
    · by_cases hs1 : s ≤ 1
      · exact hescape s ⟨hs, hs0, hs1⟩
      · have hdist : dist ((r + b) / 2) 1 ≤ dist ((r + b) / 2) s := by
          rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [hy.2]),
            abs_of_nonpos (by linarith [hy.2])]
          linarith
        exact (hescape 1 hT1).trans_le hdist
    · have hdist : dist ((r + b) / 2) 0 ≤ dist ((r + b) / 2) s := by
        rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith [hy.1]),
          abs_of_nonneg (by linarith [hy.1])]
        linarith
      exact (hescape 0 hT0).trans_le hdist

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
