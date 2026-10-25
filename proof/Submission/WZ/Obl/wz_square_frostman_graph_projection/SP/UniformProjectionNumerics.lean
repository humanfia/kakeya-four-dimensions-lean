-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.UniformProjectionNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RobustProjectionNumerics

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- Sizes of the retained rectangles and their popular intersections. -/
theorem uniform_rectangle_size_budget {δ κ : ℝ} (hδ : 0 < δ)
    (hconst : 131072 ≤ δ ^ (-κ)) :
    δ ^ (3 * κ) ≤ (δ ^ κ) ^ 2 / 16 ∧
      δ ^ (9 * κ) ≤ (((δ ^ κ) ^ 2 / 16) ^ 4 / 2) := by
  have h16 : (16 : ℝ) ≤ δ ^ (-κ) := (by norm_num : (16 : ℝ) ≤ 131072).trans hconst
  constructor
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    calc
      δ ^ (3 * κ) * 16 ≤ δ ^ (3 * κ) * δ ^ (-κ) := by gcongr
      _ = (δ ^ κ) ^ 2 := by
        rw [← Real.rpow_add hδ, ← Real.rpow_mul_natCast hδ.le]
        congr 1
        norm_num
        ring
  · have hid : ((δ ^ κ) ^ 2 / 16) ^ 4 / 2 = (δ ^ κ) ^ 8 / 131072 := by ring
    rw [hid]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 131072)).mpr
    calc
      δ ^ (9 * κ) * 131072 ≤ δ ^ (9 * κ) * δ ^ (-κ) := by gcongr
      _ = (δ ^ κ) ^ 8 := by
        rw [← Real.rpow_add hδ, ← Real.rpow_mul_natCast hδ.le]
        congr 1
        norm_num
        ring

theorem uniform_self_sum_power_budget {δ κ t N V : ℝ} (hδ : 0 < δ) (hN : 0 < N)
    (ht : δ ^ (100 * κ) ≤ t) (hV : δ ^ (5 * κ) * N ≤ V)
    (hconst : 144 ≤ δ ^ (-κ)) :
    144 * (δ ^ (-114 * κ) * N) ^ 2 / (t * V) ≤ δ ^ (-334 * κ) * N := by
  have htp : 0 < t := (Real.rpow_pos_of_pos hδ _).trans_le ht
  have hVp : 0 < V := (mul_pos (Real.rpow_pos_of_pos hδ _) hN).trans_le hV
  calc
    _ ≤ δ ^ (-κ) * (δ ^ (-114 * κ) * N) ^ 2 /
        (δ ^ (100 * κ) * (δ ^ (5 * κ) * N)) := by gcongr
    _ = (δ ^ (-κ) * (δ ^ (-114 * κ)) ^ 2 /
        (δ ^ (100 * κ) * δ ^ (5 * κ))) * N := by field_simp <;> ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ,
        ← Real.rpow_sub hδ]
      congr 2
      norm_num
      ring

theorem uniform_overlap_power_budget {δ κ t N U V : ℝ} (hδ : 0 < δ) (hN : 0 < N)
    (ht : δ ^ (100 * κ) ≤ t) (hU : δ ^ (9 * κ) * N ≤ U)
    (hV : δ ^ (11 * κ) * N ≤ V) (hconst : 5184 ≤ δ ^ (-κ)) :
    5184 * (δ ^ (-334 * κ) * N) * (δ ^ (-334 * κ) * N) * (δ ^ (-114 * κ) * N) /
        (t * U * V) ≤ δ ^ (-903 * κ) * N := by
  have htp : 0 < t := (Real.rpow_pos_of_pos hδ _).trans_le ht
  have hUp : 0 < U := (mul_pos (Real.rpow_pos_of_pos hδ _) hN).trans_le hU
  have hVp : 0 < V := (mul_pos (Real.rpow_pos_of_pos hδ _) hN).trans_le hV
  calc
    _ ≤ δ ^ (-κ) * (δ ^ (-334 * κ) * N) * (δ ^ (-334 * κ) * N) * (δ ^ (-114 * κ) * N) /
        (δ ^ (100 * κ) * (δ ^ (9 * κ) * N) * (δ ^ (11 * κ) * N)) := by gcongr
    _ = (δ ^ (-κ) * δ ^ (-334 * κ) * δ ^ (-334 * κ) * δ ^ (-114 * κ) /
        (δ ^ (100 * κ) * δ ^ (9 * κ) * δ ^ (11 * κ))) * N := by field_simp <;> ring
    _ = _ := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ,
        ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
      congr 2
      ring

theorem uniform_frostman_power_budget {δ κ C g : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hCb : C ≤ δ ^ (-κ)) (hg : δ ^ (9 * κ) ≤ g) (hconst : 2 ≤ δ ^ (-κ)) :
    2 * C / g ≤ δ ^ (-11 * κ) := by
  have hgp : 0 < g := (Real.rpow_pos_of_pos hδ _).trans_le hg
  calc
    2 * C / g ≤ δ ^ (-κ) * δ ^ (-κ) / δ ^ (9 * κ) := by gcongr
    _ = _ := by rw [← Real.rpow_add hδ, ← Real.rpow_sub hδ]; congr 1; ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
