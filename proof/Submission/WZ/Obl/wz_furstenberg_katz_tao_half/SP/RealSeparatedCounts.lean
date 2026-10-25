-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RealSeparatedCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.GridQuantization

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- An elementary interval packing bound with no integer rounding in the
conclusion. -/
theorem real_separated_ball_card {δ R c : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y)
    (hball : ∀ x ∈ S, dist x c ≤ R) :
    (S.card : ℝ) * δ ≤ 2 * R + 2 * δ := by
  classical
  let L : ℤ := ⌊(c - R) / δ⌋
  let U : ℤ := ⌊(c + R) / δ⌋
  have hLU : L ≤ U := Int.floor_mono (by apply div_le_div_of_nonneg_right _ hδ.le; linarith)
  have hsub : S.image (realGridIndex δ) ⊆ Finset.Icc L U := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hh := abs_le.mp (show |x - c| ≤ R by simpa only [Real.dist_eq] using hball x hx)
    exact Finset.mem_Icc.mpr ⟨Int.floor_mono ((div_le_div_iff_of_pos_right hδ).mpr (by linarith)),
      Int.floor_mono ((div_le_div_iff_of_pos_right hδ).mpr (by linarith))⟩
  have hSc : (S.image (realGridIndex δ)).card = S.card :=
    Finset.card_image_iff.mpr (realGridIndex_injective hδ hsep)
  have hcard := Finset.card_le_card hsub
  rw [hSc, Int.card_Icc] at hcard
  have hcardZ : (S.card : ℤ) ≤ U - L + 1 := by omega
  have hcardR : (S.card : ℝ) ≤ (U : ℝ) - (L : ℝ) + 1 := by exact_mod_cast hcardZ
  have hlow := Int.lt_floor_add_one ((c - R) / δ)
  have hhigh := Int.floor_le ((c + R) / δ)
  change (c - R) / δ < (L : ℝ) + 1 at hlow
  change (U : ℝ) ≤ (c + R) / δ at hhigh
  have hlow' := (div_lt_iff₀ hδ).mp hlow
  have hhigh' := (le_div_iff₀ hδ).mp hhigh
  nlinarith [mul_le_mul_of_nonneg_right hcardR hδ.le]

theorem real_separated_two_radius_card {δ c : ℝ} (hδ : 0 < δ) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y)
    (hball : ∀ x ∈ S, dist x c ≤ 2 * δ) : (S.card : ℝ) ≤ 6 := by
  have hh := real_separated_ball_card hδ (by positivity) S hsep hball
  nlinarith

/-- A narrow affine window contains few separated scalars when its slope
is bounded away from zero. -/
theorem real_separated_affine_window {δ q a b : ℝ} (hδ : 0 < δ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ha : q ≤ |a|) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y)
    (hwindow : ∀ x ∈ S, |a * x + b| ≤ 2 * δ) :
    q * (S.card : ℝ) ≤ 6 := by
  have hap : 0 < |a| := hq.trans_le ha
  have hane : a ≠ 0 := abs_pos.mp hap
  have hball (x : ℝ) (hx : x ∈ S) : dist x (-b / a) ≤ 2 * δ / q := by
    rw [Real.dist_eq, show x - -b / a = (a * x + b) / a by field_simp; ring, abs_div]
    exact (div_le_div_of_nonneg_right (hwindow x hx) (abs_nonneg a)).trans
      (div_le_div_of_nonneg_left (by positivity) hq ha)
  have hh := real_separated_ball_card hδ (by positivity) S hsep hball
  have hm := mul_le_mul_of_nonneg_right hh hq.le
  have hid : (2 * (2 * δ / q) + 2 * δ) * q = (4 + 2 * q) * δ := by field_simp; ring
  rw [hid] at hm
  have hfinal : (q * (S.card : ℝ)) * δ ≤ 6 * δ := by
    nlinarith [mul_le_mul_of_nonneg_left hq1 hδ.le]
  exact (mul_le_mul_iff_left₀ hδ).mp hfinal

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
