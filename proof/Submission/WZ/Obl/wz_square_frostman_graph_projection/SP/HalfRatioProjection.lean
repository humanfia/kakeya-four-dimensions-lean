-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.HalfRatioProjection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RatioDichotomy

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

noncomputable def fourProductDifference (A : Finset ℝ) : Finset ℝ :=
  ((A * A - A * A) + (A * A - A * A)) + ((A * A - A * A) + (A * A - A * A))

theorem product_difference_mem {A : Finset ℝ} {a b x : ℝ}
    (ha : a ∈ A) (hb : b ∈ A) (hx : x ∈ A) : (a - b) * x ∈ A * A - A * A := by
  rw [sub_mul]
  exact Finset.sub_mem_sub (Finset.mul_mem_mul ha hx) (Finset.mul_mem_mul hb hx)

theorem Covers.half_ratio_projection {δ q : ℝ} (hδ : 0 ≤ δ) (hq : 0 < q)
    {A : Finset ℝ} {r e : ℝ} (hr : r ∈ LargeDenominatorRatios q A) (he : e = 0 ∨ e = 1)
    {m : ℕ} {cc : Fin m → ℝ}
    (hcov : Covers δ (↑(fourProductDifference A) : Set ℝ) cc) :
    ∃ c ∈ A, ∃ d ∈ A, q ≤ |c - d| ∧ ∃ centers : Fin m → ℝ,
      Covers (δ / |c - d|) ((fun p : ℝ × ℝ => p.1 + ((r + e) / 2) * p.2) ''
        (↑(A ×ˢ A) : Set (ℝ × ℝ))) centers := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hden, rfl⟩ := hr
  have hdenp : 0 < |c - d| := hq.trans_le hden
  have hne : c - d ≠ 0 := abs_pos.mp hdenp
  have hne2 : 2 * (c - d) ≠ 0 := mul_ne_zero (by norm_num) hne
  refine ⟨c, hc, d, hd, hden, fun j => cc j / (2 * (c - d)), ?_⟩
  rintro z ⟨p, hp, rfl⟩
  have hp' := Finset.mem_product.mp hp
  have h1 := product_difference_mem hc hd hp'.1
  have h2 := product_difference_mem ha hb hp'.2
  have h3 := product_difference_mem hc hd hp'.2
  have h0 : (0 : ℝ) ∈ A * A - A * A := by
    simpa only [sub_self, zero_mul] using product_difference_mem ha ha ha
  have hmem : (2 * (c - d)) * (p.1 + (((a - b) / (c - d) + e) / 2) * p.2) ∈
      fourProductDifference A := by
    rcases he with rfl | rfl
    · have hid : (2 * (c - d)) * (p.1 + (((a - b) / (c - d) + 0) / 2) * p.2) =
          ((c - d) * p.1 + (c - d) * p.1) + ((a - b) * p.2 + 0) := by field_simp <;> ring
      rw [hid]
      exact Finset.add_mem_add (Finset.add_mem_add h1 h1) (Finset.add_mem_add h2 h0)
    · have hid : (2 * (c - d)) * (p.1 + (((a - b) / (c - d) + 1) / 2) * p.2) =
          ((c - d) * p.1 + (c - d) * p.1) + ((a - b) * p.2 + (c - d) * p.2) := by
        field_simp <;> ring
      rw [hid]
      exact Finset.add_mem_add (Finset.add_mem_add h1 h1) (Finset.add_mem_add h2 h3)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hmem)
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  change dist (p.1 + (((a - b) / (c - d) + e) / 2) * p.2)
    (cc j / (2 * (c - d))) ≤ δ / |c - d|
  have hid : p.1 + (((a - b) / (c - d) + e) / 2) * p.2 - cc j / (2 * (c - d)) =
      ((2 * (c - d)) * (p.1 + (((a - b) / (c - d) + e) / 2) * p.2) - cc j) /
        (2 * (c - d)) := by field_simp
  rw [Real.dist_eq, hid, abs_div]
  have hden2 : |c - d| ≤ |2 * (c - d)| := by rw [abs_mul]; norm_num; linarith [abs_nonneg (c - d)]
  have hj' : |(2 * (c - d)) * (p.1 + (((a - b) / (c - d) + e) / 2) * p.2) - cc j| ≤ δ := by
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hj
  exact (div_le_div_of_nonneg_right hj' (abs_nonneg _)).trans
    (div_le_div_of_nonneg_left hδ hdenp hden2)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
