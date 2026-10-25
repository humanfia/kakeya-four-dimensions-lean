-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RatioDichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.DenseRatioProducts
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.HalfEscape

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

theorem LargeDenominatorRatios.finite (q : ℝ) (A : Finset ℝ) :
    (LargeDenominatorRatios q A).Finite := by
  classical
  let P := ((A ×ˢ A) ×ˢ (A ×ˢ A)).image
    (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (p.1.1 - p.1.2) / (p.2.1 - p.2.2))
  apply P.finite_toSet.subset
  rintro t ⟨a, ha, b, hb, c, hc, d, hd, hcd, rfl⟩
  exact Finset.mem_image.mpr ⟨((a, b), (c, d)),
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
      Finset.mem_product.mpr ⟨hc, hd⟩⟩, rfl⟩

theorem LargeDenominatorRatios.zero_one {q : ℝ} (hq : 0 < q) {A : Finset ℝ}
    (hpair : ∃ c ∈ A, ∃ d ∈ A, q ≤ |c - d|) :
    (0 : ℝ) ∈ LargeDenominatorRatios q A ∧ (1 : ℝ) ∈ LargeDenominatorRatios q A := by
  obtain ⟨c, hc, d, hd, hcd⟩ := hpair
  have hne : c - d ≠ 0 := abs_pos.mp (hq.trans_le hcd)
  exact ⟨⟨c, hc, c, hc, c, hc, d, hd, hcd, by simp⟩,
    ⟨c, hc, d, hd, c, hc, d, hd, hcd, by simp [hne]⟩⟩

theorem interval_dense_of_full_dense {T : Set ℝ} (h0 : (0 : ℝ) ∈ T) (h1 : (1 : ℝ) ∈ T)
    {r : ℝ} (hdense : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ T, dist t x ≤ r) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ T, t ∈ Set.Icc (0 : ℝ) 1 ∧ dist t x ≤ r := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := hdense x hx
  by_cases ht0 : 0 ≤ t
  · by_cases ht1 : t ≤ 1
    · exact ⟨t, ht, ⟨ht0, ht1⟩, htx⟩
    · refine ⟨1, h1, ⟨by norm_num, le_rfl⟩, ?_⟩
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.2] : 0 ≤ 1 - x)]
      have hh := abs_le.mp (show |t - x| ≤ r by simpa only [Real.dist_eq] using htx)
      linarith
  · refine ⟨0, h0, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [dist_zero_left, Real.norm_of_nonneg hx.1]
    have hh := abs_le.mp (show |t - x| ≤ r by simpa only [Real.dist_eq] using htx)
    linarith

/-- Either the ratio family is dense or one elementary affine operation
escapes from it by a definite amount. -/
theorem large_ratio_dichotomy {q h : ℝ} (hq : 0 < q) (A : Finset ℝ)
    (hpair : ∃ c ∈ A, ∃ d ∈ A, q ≤ |c - d|) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ LargeDenominatorRatios q A,
      t ∈ Set.Icc (0 : ℝ) 1 ∧ dist t x ≤ 2 * h) ∨
    ∃ r ∈ LargeDenominatorRatios q A, ∃ b : ℝ, (b = 0 ∨ b = 1) ∧
      ∀ s ∈ LargeDenominatorRatios q A, h < dist ((r + b) / 2) s := by
  classical
  have h01 := LargeDenominatorRatios.zero_one hq hpair
  by_cases hdense : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∃ t ∈ LargeDenominatorRatios q A, dist t x ≤ 2 * h
  · exact Or.inl (interval_dense_of_full_dense h01.1 h01.2 hdense)
  · right
    push Not at hdense
    apply exists_half_escape (LargeDenominatorRatios.finite q A).isCompact ⟨0, h01.1⟩
    obtain ⟨x, hx, hfar⟩ := hdense
    exact ⟨x, hx, fun s hs => by simpa only [dist_comm] using hfar s hs⟩

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
