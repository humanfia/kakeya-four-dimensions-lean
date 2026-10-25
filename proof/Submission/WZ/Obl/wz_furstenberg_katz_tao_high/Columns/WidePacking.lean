-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.WidePacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0720 Columns/WidePacking.lean (758215d).
-- Adapted from local o157/x0675 High/WideStripPacking.lean (itself from local o141/x0563).
import Submission.WZ.Obl.wz_osw_single_scale_heavy_pairs.StripCount
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.CircleGeometry

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs
open scoped BigOperators Classical

/-- A framed strip count with separate incidence width and label separation. -/
theorem wide_frame_count {u y : E2} {r a w : ℝ} (hu : ‖u‖ = 1)
    (hr : 0 < r) (ha : 0 ≤ a) (hw : 0 ≤ w)
    (J : Finset (E2 × E2)) (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    (hJ : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖y - j.1‖ ≤ 8 ∧
      (inner ℝ j.2 u) ^ 2 ≤ 1 / 2 ∧ |inner ℝ j.2 u| ≤ a ∧
      |inner ℝ (y - j.1) j.2| ≤ w) :
    (J.card : ℝ) ≤ 2 * (64 * a / r + 2) * (4 * w / r + 2) := by
  classical
  let box : Finset (ℤ × ℤ × ℤ) := Finset.Icc 0 1 ×ˢ
    (Finset.Icc ⌊-(32 * a / r)⌋ ⌊32 * a / r⌋ ×ˢ
      Finset.Icc ⌊-(2 * w / r)⌋ ⌊2 * w / r⌋)
  have hmaps : Set.MapsTo (stripCode u y (r / 32) (r / 2)) (↑J) (↑box) := by
    intro j hj
    obtain ⟨_, _, _, hangle, hoff⟩ := hJ j hj
    simp only [box, stripCode, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨by split_ifs <;> norm_num, by split_ifs <;> norm_num⟩,
      ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩,
      ⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩⟩
    · apply (le_div_iff₀ (by positivity : 0 < r / 32)).mpr
      field_simp
      nlinarith [(abs_le.mp hangle).1]
    · apply (div_le_iff₀ (by positivity : 0 < r / 32)).mpr
      field_simp
      nlinarith [(abs_le.mp hangle).2]
    · apply (le_div_iff₀ (by positivity : 0 < r / 2)).mpr
      field_simp
      nlinarith [(abs_le.mp hoff).1]
    · apply (div_le_iff₀ (by positivity : 0 < r / 2)).mpr
      field_simp
      nlinarith [(abs_le.mp hoff).2]
  have hinj := stripCode_injOn hu (show 0 < r / 32 by positivity)
    (show 0 < r / 2 by positivity) (by linarith) hsep
    (fun j hj => ⟨(hJ j hj).1, (hJ j hj).2.1, (hJ j hj).2.2.1⟩)
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  have ha' := card_Icc_floor_le (show 0 ≤ 32 * a / r by positivity)
  have hw' := card_Icc_floor_le (show 0 ≤ 2 * w / r by positivity)
  have hbox : (box.card : ℝ) ≤ 2 * (64 * a / r + 2) * (4 * w / r + 2) := by
    simp only [box, Finset.card_product]
    push_cast
    have h01 : ((Finset.Icc (0 : ℤ) 1).card : ℝ) = 2 := by norm_num
    rw [h01]
    have hmul := mul_le_mul ha' hw' (Nat.cast_nonneg _)
      (show 0 ≤ 2 * (32 * a / r) + 2 by positivity)
    convert mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  exact (Nat.cast_le.mpr hcard).trans hbox


end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
