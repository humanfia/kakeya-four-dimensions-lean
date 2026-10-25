-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.BoxNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_flat_factored_improvement.FlatMap

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (StandardPrism flatMap flatMap_apply flatScales flatScales_pos)

noncomputable def normalCenter (b : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Space :=
  e.symm (WithLp.toLp 2 ![e z 0, if b ≤ 2 then e z 1 else 0, 0])

noncomputable def normalFrame (b : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    Space ≃ᵃⁱ[ℝ] Space := boxFrame (normalCenter b z e) e

@[simp] lemma normalFrame_coord_zero (b : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (p : Space) :
    (normalFrame b z e).symm p 0 = e (p - z) 0 := by
  simp [normalFrame, normalCenter, map_sub]

@[simp] lemma normalFrame_coord_one (b : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (p : Space) :
    (normalFrame b z e).symm p 1 = if b ≤ 2 then e (p - z) 1 else e p 1 := by
  by_cases hb : b ≤ 2 <;> simp [normalFrame, normalCenter, map_sub, hb]

@[simp] lemma normalFrame_coord_two (b : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (p : Space) :
    (normalFrame b z e).symm p 2 = e p 2 := by
  simp [normalFrame, normalCenter, map_sub]

lemma box_unitBall_subset_normalPrism {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    Box a b c z e ∩ closedBall (0 : Space) 1 ⊆
      normalFrame b z e '' StandardPrism a (min b 2) := by
  intro p hp
  refine ⟨(normalFrame b z e).symm p, ?_, (normalFrame b z e).apply_symm_apply p⟩
  have hcoord (i : Fin 3) : |e p i| ≤ 1 := by
    have hh : |e p i| ≤ ‖e p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e p) i
    rw [e.norm_map] at hh
    exact hh.trans (mem_closedBall_zero_iff.mp hp.2)
  refine ⟨?_, ?_, ?_⟩
  · rw [normalFrame_coord_zero]
    exact hp.1.1.trans (by linarith)
  · rw [normalFrame_coord_one]
    by_cases hb2 : b ≤ 2
    · rw [if_pos hb2, min_eq_left hb2]
      exact hp.1.2.1.trans (by linarith)
    · rw [if_neg hb2, min_eq_right (le_of_not_ge hb2)]
      exact (hcoord 1).trans (by norm_num)
  · rw [normalFrame_coord_two]
    exact (hcoord 2).trans (by norm_num)

/-- The normalization keeps doubled coarse tubes bounded, even when the original
box has long side between one and eight or its middle side exceeds two. -/
lemma flatMap_triple_box_bounded {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    flatMap (normalFrame b z e) a (min b 2) ha (lt_min hb (by norm_num)) ''
      (Box (3 * a) (3 * b) (3 * c) z e ∩ closedBall (0 : Space) 4) ⊆
        closedBall (0 : Space) 1 := by
  rintro _ ⟨p, hp, rfl⟩
  have hcoord (i : Fin 3) : |e p i| ≤ 4 := by
    have hh : |e p i| ≤ ‖e p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e p) i
    rw [e.norm_map] at hh
    exact hh.trans (mem_closedBall_zero_iff.mp hp.2)
  have hi (i : Fin 3) :
      |flatMap (normalFrame b z e) a (min b 2) ha (lt_min hb (by norm_num)) p i| ≤ 1 / 2 := by
    rw [flatMap_apply, abs_mul, abs_of_pos (flatScales_pos ha (lt_min hb (by norm_num)) i)]
    fin_cases i
    · change 1 / (4 * a) * |(normalFrame b z e).symm p 0| ≤ _
      rw [normalFrame_coord_zero]
      have hh := mul_le_mul_of_nonneg_left hp.1.1 (by positivity : 0 ≤ 1 / (4 * a))
      have he : 1 / (4 * a) * (3 * a / 2) = (3 : ℝ) / 8 := by field_simp; ring
      exact (hh.trans_eq he).trans (by norm_num)
    · change 1 / (4 * min b 2) * |(normalFrame b z e).symm p 1| ≤ _
      rw [normalFrame_coord_one]
      by_cases hb2 : b ≤ 2
      · rw [if_pos hb2, min_eq_left hb2]
        have hh := mul_le_mul_of_nonneg_left hp.1.2.1 (by positivity : 0 ≤ 1 / (4 * b))
        have he : 1 / (4 * b) * (3 * b / 2) = (3 : ℝ) / 8 := by field_simp; ring
        exact (hh.trans_eq he).trans (by norm_num)
      · rw [if_neg hb2, min_eq_right (le_of_not_ge hb2)]
        norm_num
        linarith [hcoord 1]
    · change 1 / 8 * |(normalFrame b z e).symm p 2| ≤ _
      rw [normalFrame_coord_two]
      linarith [hcoord 2]
  apply mem_closedBall_zero_iff.mpr
  convert WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hi using 1 <;> norm_num

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
