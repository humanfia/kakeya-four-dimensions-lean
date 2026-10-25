-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RobustProjectionNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RectangularNumerics
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.PopularScalarFamily

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products


/-- Solving the three-path inequality loses only polynomial factors in
the graph density and the lower slope cutoff. -/
theorem graph_projection_bound {c d N M X K J m n : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hN : 0 < N) (hM : 0 < M)
    (hX : 0 ≤ X) (hK : 0 ≤ K) (hJ : 0 ≤ J) (hm : 0 ≤ m)
    (hsize : (d / 4) * N ≤ X) (hratio : N ≤ J * M)
    (hmK : m ≤ K * N)
    (hcount : c * (d ^ 7 / 524288) * N * M * n ≤ 288 * m ^ 3) :
    n ≤ (603979776 * K ^ 3 * J / (c * d ^ 8)) * X := by
  have hden : 0 < c * (d ^ 7 / 524288) * N * M := by positivity
  have hNX : N ≤ (4 / d) * X := by
    have hh : N ≤ (4 * X) / d := (le_div_iff₀ hd).mpr (by nlinarith)
    convert hh using 1 <;> ring
  have hratio' : N / M ≤ J := (div_le_iff₀ hM).mpr hratio
  calc
    n ≤ 288 * m ^ 3 / (c * (d ^ 7 / 524288) * N * M) :=
      (le_div_iff₀ hden).mpr (by nlinarith [hcount])
    _ ≤ 288 * (K * N) ^ 3 / (c * (d ^ 7 / 524288) * N * M) := by gcongr
    _ = (150994944 * K ^ 3 / (c * d ^ 7)) * (N / M) * N := by
      field_simp
      <;> ring
    _ ≤ (150994944 * K ^ 3 / (c * d ^ 7)) * J * ((4 / d) * X) := by gcongr
    _ = _ := by field_simp <;> ring

/-- The numerical cost in the robust Cartesian reduction. -/
theorem robust_projection_power_budget {δ κ : ℝ} (hδ : 0 < δ)
    (hconst : 603979776 ≤ δ ^ (-κ)) :
    603979776 * (δ ^ (-κ)) ^ 3 * δ ^ (-2 * κ) /
        (δ ^ (100 * κ) * (δ ^ κ) ^ 8) ≤ δ ^ (-114 * κ) := by
  calc
    _ ≤ δ ^ (-κ) * (δ ^ (-κ)) ^ 3 * δ ^ (-2 * κ) /
        (δ ^ (100 * κ) * (δ ^ κ) ^ 8) := by gcongr
    _ = _ := by
      rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_mul_natCast hδ.le,
        ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
      congr 1
      norm_num
      ring

theorem robust_frostman_power_budget {δ κ C : ℝ} (hδ : 0 < δ) (hC0 : 0 ≤ C)
    (hC : C ≤ δ ^ (-κ)) (hconst : 16 ≤ δ ^ (-κ)) :
    C / ((δ ^ κ) ^ 2 / 16) ≤ δ ^ (-4 * κ) := by
  calc
    _ = 16 * C / (δ ^ κ) ^ 2 := by ring
    _ ≤ δ ^ (-κ) * δ ^ (-κ) / (δ ^ κ) ^ 2 := by gcongr
    _ = _ := by
      rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
      congr 1
      norm_num
      ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
