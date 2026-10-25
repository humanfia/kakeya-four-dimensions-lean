-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarClosureNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarClosure
namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
theorem scalar_closure_bound_pow {c K x : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hK : 1 ≤ K)
    (hx : 1000 ≤ x) (hKx : K ≤ x) (hcx : c⁻¹ ≤ x) :
    scalarClosureBound c K ≤ x ^ 25 := by
  unfold scalarClosureBound
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hx4 : x ≤ x ^ 4 := le_self_pow₀ hx1 (by norm_num)
  have hprod : 144 * K ^ 2 / c ≤ x ^ 4 := by
    calc
      144 * K ^ 2 / c = 144 * K ^ 2 * c⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ x * x ^ 2 * x := by gcongr <;> linarith
      _ = _ := by ring
  have hinput : 6 * (K + 144 * K ^ 2 / c + 144 * K ^ 2 / c) ≤ x ^ 5 := by
    calc
      _ ≤ 18 * x ^ 4 := by linarith
      _ ≤ x * x ^ 4 := by gcongr; linarith
      _ = _ := by ring
  have hinput' : 6 * (K + K + K) ≤ x ^ 5 := by
    calc
      _ ≤ 18 * x ^ 4 := by linarith
      _ ≤ x * x ^ 4 := by gcongr; linarith
      _ = _ := by ring
  have hlarge : 9 * (6 * (K + 144 * K ^ 2 / c + 144 * K ^ 2 / c)) ^ 3 ≤ x ^ 16 := by
    calc
      _ ≤ x * (x ^ 5) ^ 3 := by gcongr <;> linarith
      _ = _ := by ring
  have hlarge' : 9 * (6 * (K + K + K)) ^ 3 ≤ x ^ 16 := by
    calc
      _ ≤ x * (x ^ 5) ^ 3 := by gcongr <;> linarith
      _ = _ := by ring
  have hbase : 9 * (6 * K) ^ 3 ≤ x ^ 7 := by
    calc
      _ ≤ x * (x * x) ^ 3 := by gcongr <;> linarith
      _ = _ := by ring
  calc
    _ ≤ x + 288 * x ^ 7 * (x ^ 16 + x ^ 16) := by gcongr
    _ = x + 576 * x ^ 23 := by ring
    _ ≤ x ^ 23 + x * x ^ 23 := by gcongr <;> first | linarith | exact le_self_pow₀ hx1 (by norm_num)
    _ = (1 + x) * x ^ 23 := by ring
    _ ≤ x ^ 2 * x ^ 23 := by gcongr; nlinarith
    _ = _ := by ring

/-- One algebraic enlargement costs at most a factor one hundred in the
small exponent used to budget scalar projections. -/
theorem scalar_closure_rpow_bound {δ d : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : 0 < d)
    (hconst : 1000 ≤ δ ^ (-d)) :
    scalarClosureBound (δ ^ d) (δ ^ (-d)) ≤ δ ^ (-(100 * d)) := by
  have hp : 0 < δ ^ d := Real.rpow_pos_of_pos hδ _
  have hc1 : δ ^ d ≤ 1 := Real.rpow_le_one hδ.le hδ1 hd.le
  have hK : 1 ≤ δ ^ (-d) := by linarith
  have hinv : (δ ^ d)⁻¹ ≤ δ ^ (-d) := by rw [Real.rpow_neg hδ.le]
  calc
    _ ≤ (δ ^ (-d)) ^ (25 : ℕ) :=
      scalar_closure_bound_pow hp hc1 hK hconst le_rfl hinv
    _ = δ ^ (-(25 * d)) := by
      rw [← Real.rpow_mul_natCast hδ.le]
      congr 1
      norm_num
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
