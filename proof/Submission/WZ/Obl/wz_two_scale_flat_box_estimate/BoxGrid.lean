-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.BoxGrid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_flat_factored_improvement.GridHull

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (shortMap shortMap_apply shortScales)
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridUnion gridCell gridCell_dist_lt gridUnion_volumeReal gridUnion_volume_ne_top)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (closedTube)

lemma nearby_box {a b c r : ℝ} {p q z : Space} {e : Space ≃ₗᵢ[ℝ] Space}
    (hq : q ∈ Box a b c z e) (h : dist p q ≤ r) :
    p ∈ Box (a + 2 * r) (b + 2 * r) (c + 2 * r) z e := by
  have hcoord (i : Fin 3) (w : ℝ) (hi : |e (q - z) i| ≤ w / 2) :
      |e (p - z) i| ≤ (w + 2 * r) / 2 := by
    have he : e (p - z) = e (p - q) + e (q - z) := by rw [← map_add]; congr 1; abel
    have hd : |e (p - q) i| ≤ r := by
      have hh : |e (p - q) i| ≤ ‖e (p - q)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e (p - q)) i
      rw [e.norm_map] at hh
      exact hh.trans (by simpa only [dist_eq_norm] using h)
    rw [he]
    change |e (p - q) i + e (q - z) i| ≤ _
    exact (abs_add_le _ _).trans (by linarith)
  exact ⟨hcoord 0 a hq.1, hcoord 1 b hq.2.1, hcoord 2 c hq.2.2⟩

lemma thickTube_box_subset {ρ a b c R : ℝ} (hρ : 0 < ρ)
    {x v z : Space} {e : Space ≃ₗᵢ[ℝ] Space}
    (hT : Tube ρ x v ⊆ Box a b c z e) :
    closedTube R x v ⊆ Box (a + 2 * R) (b + 2 * R) (c + 2 * R) z e := by
  apply closure_minimal _ (box_isClosed _ _ _ _ _)
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  exact nearby_box (hT (self_subset_thickening hρ _ hq)) hpq.le

lemma shortMap_box_tubes_bounded {ρ a b c : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    (haSmall : a ≤ 1 / 100) (hbc : b ≤ c) (hc8 : c ≤ 8)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) {x v : Space}
    (hT : Tube ρ x v ⊆ Box a b c z e) :
    shortMap (boxFrame z e) a ha '' closedTube (3 * a) x v ⊆ closedBall (0 : Space) 1 := by
  rintro _ ⟨p, hp, rfl⟩
  have hbox := thickTube_box_subset hρ hT hp
  have hi (i : Fin 3) : |shortMap (boxFrame z e) a ha p i| ≤ 1 / 8 := by
    rw [shortMap_apply, abs_mul]
    fin_cases i
    · change |1 / (64 * a)| * |e (p - z) 0| ≤ _
      rw [abs_of_pos (by positivity : 0 < 1 / (64 * a))]
      have hh := mul_le_mul_of_nonneg_left hbox.1 (by positivity : 0 ≤ 1 / (64 * a))
      have he : 1 / (64 * a) * ((a + 2 * (3 * a)) / 2) = (7 : ℝ) / 128 := by field_simp; ring
      exact (hh.trans_eq he).trans (by norm_num)
    · change |(1 / 64 : ℝ)| * |e (p - z) 1| ≤ _
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 64)]
      have hh := hbox.2.1
      linarith
    · change |(1 / 64 : ℝ)| * |e (p - z) 2| ≤ _
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 64)]
      have hh := hbox.2.2
      linarith
  apply mem_closedBall_zero_iff.mpr
  have hh := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le
    (by norm_num : (0 : ℝ) ≤ 1 / 8) hi
  linarith

lemma gridUnion_box_subset {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (s : Finset (Fin 3 → ℤ))
    (hmeet : ∀ k ∈ s, (Box a b c z e ∩ gridCell a k).Nonempty) :
    gridUnion a s ⊆ Box (6 * a) (6 * b) (6 * c) z e := by
  intro p hp
  obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp hp
  obtain ⟨q, hq, hqk⟩ := hmeet k hk
  have hh := nearby_box hq (gridCell_dist_lt ha hpk hqk).le
  exact ⟨hh.1.trans (by linarith), hh.2.1.trans (by linarith), hh.2.2.trans (by linarith)⟩

lemma gridUnion_box_volume {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc8 : c ≤ 8) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (s : Finset (Fin 3 → ℤ))
    (hmeet : ∀ k ∈ s, (Box a b c z e ∩ gridCell a k).Nonempty) :
    volume (gridUnion a s) ≤ ENNReal.ofReal (1728 * a * b) := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  calc
    _ ≤ volume (Box (6 * a) (6 * b) (6 * c) z e) :=
      measure_mono (gridUnion_box_subset ha hab hbc z e s hmeet)
    _ = ENNReal.ofReal ((6 * a) * (6 * b) * (6 * c)) :=
      box_volume (by positivity) (by positivity) (by positivity) z e
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hc8 (by positivity : 0 ≤ a * b)])

lemma grid_box_capacity {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc8 : c ≤ 8) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (s : Finset (Fin 3 → ℤ))
    (hmeet : ∀ k ∈ s, (Box a b c z e ∩ gridCell a k).Nonempty) :
    (s.card : ℝ) * a ^ 3 ≤ 1728 * a * b := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (gridUnion_box_volume ha hab hbc hc8 z e s hmeet)
  simpa only [← measureReal_def, gridUnion_volumeReal ha,
    ENNReal.toReal_ofReal (by have hb := ha.trans_le hab; positivity : 0 ≤ 1728 * a * b)] using hh

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
