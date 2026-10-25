-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ProductSumContainment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.HalfRatioProjection

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped Pointwise

theorem four_product_difference_eq (A : Finset ℝ) :
    fourProductDifference A = (4 : ℕ) • (A * A) - (4 : ℕ) • (A * A) := by
  let B := A * A
  change ((B - B) + (B - B)) + ((B - B) + (B - B)) = (4 : ℕ) • B - (4 : ℕ) • B
  calc
    ((B - B) + (B - B)) + ((B - B) + (B - B)) = (4 : ℕ) • (B - B) := by
      rw [show (4 : ℕ) = 2 + 2 by decide, add_nsmul, two_nsmul]
    _ = _ := nsmul_sub B B 4

/-- If `1` is among the factors, the ring expression is contained in nine
signed summands from the product set. -/
theorem ring_expression_subset_nine_products (A : Finset ℝ) (h1 : (1 : ℝ) ∈ A) :
    A + fourProductDifference A ⊆ (5 : ℕ) • (A * A) - (4 : ℕ) • (A * A) := by
  classical
  rw [four_product_difference_eq]
  intro x hx
  obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_sub.mp hy
  have haB : a ∈ A * A := by simpa only [one_mul] using Finset.mul_mem_mul h1 ha
  have hab : a + b ∈ (5 : ℕ) • (A * A) := by
    have haa : a ∈ (1 : ℕ) • (A * A) := by simpa only [one_nsmul] using haB
    have hh := Finset.add_mem_add haa hb
    simpa only [← add_nsmul] using hh
  have hh := Finset.sub_mem_sub hab hc
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
