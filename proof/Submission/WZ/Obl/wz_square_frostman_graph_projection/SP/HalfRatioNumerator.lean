-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.HalfRatioNumerator.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.HalfRatioProjection

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

/-- Bounded escaping ratios have numerator projections in a short interval
inside the four-product sum-difference set. -/
theorem half_ratio_numerator {q r e : ℝ} (hq : 0 < q) (A : Finset ℝ)
    (hA : ∀ a ∈ A, a ∈ Set.Icc (0 : ℝ) 1)
    (hr : r ∈ LargeDenominatorRatios q A) (hrI : r ∈ Set.Icc (0 : ℝ) 1)
    (he : e = 0 ∨ e = 1) :
    ∃ c ∈ A, ∃ d ∈ A, q ≤ |c - d| ∧ ∃ T : Finset ℝ,
      T ⊆ fourProductDifference A ∧ (∀ x ∈ T, |x| ≤ 4 * |c - d|) ∧
      ∀ a ∈ A, ∀ b ∈ A, 2 * (c - d) * (a + ((r + e) / 2) * b) ∈ T := by
  classical
  have ht : (r + e) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    rcases he with rfl | rfl <;> constructor <;> linarith [hrI.1, hrI.2]
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hden, heq⟩ := hr
  have hne : c - d ≠ 0 := abs_pos.mp (hq.trans_le hden)
  let T := (A ×ˢ A).image (fun p : ℝ × ℝ => 2 * (c - d) * (p.1 + ((r + e) / 2) * p.2))
  refine ⟨c, hc, d, hd, hden, T, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hp' := Finset.mem_product.mp hp
    have h1 := product_difference_mem hc hd hp'.1
    have h2 := product_difference_mem ha hb hp'.2
    have h3 := product_difference_mem hc hd hp'.2
    have h0 : (0 : ℝ) ∈ A * A - A * A := by
      simpa only [sub_self, zero_mul] using product_difference_mem ha ha ha
    rw [heq]
    rcases he with rfl | rfl
    · have hid : 2 * (c - d) * (p.1 + (((a - b) / (c - d) + 0) / 2) * p.2) =
          ((c - d) * p.1 + (c - d) * p.1) + ((a - b) * p.2 + 0) := by
        field_simp <;> ring
      rw [hid]
      exact Finset.add_mem_add (Finset.add_mem_add h1 h1) (Finset.add_mem_add h2 h0)
    · have hid : 2 * (c - d) * (p.1 + (((a - b) / (c - d) + 1) / 2) * p.2) =
          ((c - d) * p.1 + (c - d) * p.1) + ((a - b) * p.2 + (c - d) * p.2) := by
        field_simp <;> ring
      rw [hid]
      exact Finset.add_mem_add (Finset.add_mem_add h1 h1) (Finset.add_mem_add h2 h3)
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have ha' := hA p.1 (Finset.mem_product.mp hp).1
    have hb' := hA p.2 (Finset.mem_product.mp hp).2
    have hnonneg : 0 ≤ p.1 + ((r + e) / 2) * p.2 :=
      add_nonneg ha'.1 (mul_nonneg ht.1 hb'.1)
    have hbound : p.1 + ((r + e) / 2) * p.2 ≤ 2 := by nlinarith [ha'.2, mul_le_mul ht.2 hb'.2 hb'.1 (by norm_num : (0 : ℝ) ≤ 1)]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hnonneg]
    nlinarith [abs_nonneg (c - d)]
  · intro x hx y hy
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
