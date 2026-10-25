-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FlatScales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FlatScales.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FlatScales.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- A flat slab supplies a filling length and a wider intermediate box. -/
theorem flat_filling_scales_of_small_slab {δ R r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (hrsmall : r ≤ 1 / 100) (hflat : 100 * r ≤ R) :
    let L := δ / (16 * r)
    let B := 2 * R * δ / r
    B = 32 * R * L ∧ 3 * δ ≤ L ∧ 1 / 2 + δ + L ≤ 1 ∧
      2 * δ ≤ B ∧ 3 * δ + 8 * r * (L + 2 * δ) ≤ 5 * δ ∧
      3 * δ + 8 * R * (L + 2 * δ) ≤ B / 2 := by
  have hr : 0 < r := hδ.trans_le hδr
  have hRpos : 0 < R := by linarith
  dsimp only
  refine ⟨by field_simp; ring, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity : 0 < 16 * r)]
    nlinarith [mul_le_mul_of_nonneg_left hrsmall hδ.le]
  · have hL : δ / (16 * r) ≤ (1 / 16 : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < 16 * r)]
      linarith
    linarith
  · rw [le_div_iff₀ hr]
    nlinarith [mul_le_mul_of_nonneg_left hflat hδ.le]
  · have he : 3 * δ + 8 * r * (δ / (16 * r) + 2 * δ) = 7 * δ / 2 + 16 * r * δ := by
      field_simp
      ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hrsmall hδ.le]
  · have he : 2 * R * δ / r / 2 - (3 * δ + 8 * R * (δ / (16 * r) + 2 * δ)) =
        (δ / (2 * r)) * (R - 6 * r - 32 * R * r) := by
      field_simp
      ring
    have hprod : 32 * R * r ≤ (8 / 25 : ℝ) * R := by
      nlinarith [mul_le_mul_of_nonneg_left hrsmall hRpos.le]
    have hnon : 0 ≤ R - 6 * r - 32 * R * r := by linarith
    have hh : 0 ≤ (δ / (2 * r)) * (R - 6 * r - 32 * R * r) := by positivity
    rw [← he] at hh
    linarith

/-- Backwards-compatible bounded-radius version. -/
theorem flat_filling_scales {δ R r : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (hrsmall : r ≤ 1 / 100) (hflat : 100 * r ≤ R) (_hR : R ≤ 1) :
    let L := δ / (16 * r)
    let B := 2 * R * δ / r
    B = 32 * R * L ∧ 3 * δ ≤ L ∧ 1 / 2 + δ + L ≤ 1 ∧
      2 * δ ≤ B ∧ 3 * δ + 8 * r * (L + 2 * δ) ≤ 5 * δ ∧
      3 * δ + 8 * R * (L + 2 * δ) ≤ B / 2 :=
  flat_filling_scales_of_small_slab hδ hδr hrsmall hflat

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
