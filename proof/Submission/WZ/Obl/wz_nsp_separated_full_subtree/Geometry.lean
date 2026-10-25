-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_separated_full_subtree.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_cover_refinement.Covers

namespace WangZahlLot.Obl.wz_nsp_separated_full_subtree

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube (r : ℝ) (x v : Space) : Set Space :=
  thickening r (segment ℝ x (x + v))

/-- The relation used for every layer, including the fine layer. -/
def Near (r : ℝ) (x v y w : Space) : Prop :=
  (Tube r x v ∩ Tube r y w).Nonempty ∧ min ‖v - w‖ ‖v + w‖ < 100000 * r

lemma near_symm {r : ℝ} {x v y w : Space} (h : Near r x v y w) :
    Near r y w x v := by
  refine ⟨?_, ?_⟩
  · simpa only [inter_comm] using h.1
  · simpa only [norm_sub_rev w v, add_comm w v] using h.2

lemma separated_of_not_near {r : ℝ} (hr : 0 < r) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (h : ¬Near r x v y w) :
    volume (Tube r x v ∩ Tube r y w) ≤ (1 / 2 : ENNReal) * volume (Tube r x v) := by
  by_cases hI : (Tube r x v ∩ Tube r y w).Nonempty
  · have hd : 100000 * r ≤ min ‖v - w‖ ‖v + w‖ :=
      le_of_not_gt (fun hd => h ⟨hI, hd⟩)
    exact WangZahlLot.Obl.wz_direction_density_transfer.intersection_le_half hr hv hw
      (hd.trans (min_le_left _ _)) (hd.trans (min_le_right _ _))
  · rw [Set.not_nonempty_iff_eq_empty.mp hI, measure_empty]
    exact zero_le

lemma contained_direction_close {δ r : ℝ} (hδ : 0 < δ) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (h : Tube δ x v ⊆ Tube r y w) :
    min ‖v - w‖ ‖v + w‖ < 4 * r := by
  obtain ⟨a, ha, hxa⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube
    (h (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))))
  obtain ⟨b, hb, hxb⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube
    (h (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v))))
  have he : v - (b - a) • w = (x + v - (y + b • w)) - (x - (y + a • w)) := by module
  have hn : ‖v - (b - a) • w‖ < 2 * r := by
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hs := WangZahlLot.Obl.wz_direction_density_transfer.scale_sep
    (a := 1) (b := b - a) hv hw (min_le_left _ _) (min_le_right _ _)
  simp only [abs_one, mul_one, one_smul] at hs
  linarith

lemma near_of_common_child {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    {x v y w y' w' : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1)
    (h : Tube δ x v ⊆ Tube r y w) (h' : Tube δ x v ⊆ Tube r y' w') :
    Near r y w y' w' := by
  have hx := self_subset_thickening hδ (segment ℝ x (x + v)) (left_mem_segment ℝ x (x + v))
  refine ⟨⟨x, h hx, h' hx⟩, ?_⟩
  have h1 := contained_direction_close hδ hv hw h
  have h2 := contained_direction_close hδ hv hw' h'
  have ht := WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd_triangle w v w'
  dsimp only [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd] at ht
  rw [norm_sub_rev w v, add_comm w v] at ht
  linarith

abbrev Wide (r : ℝ) (x v : Space) : Set Space :=
  WangZahlLot.Obl.wz_separated_cover_refinement.Container (1000 * r) x v

lemma wide_convex (r : ℝ) (x v : Space) : Convex ℝ (Wide r x v) := by
  exact Convex.affine_image _ ((convex_segment _ _).thickening _)

/-- A conflicting tube is contained in one convex cylinder of controlled volume. -/
lemma near_subset_wide {r : ℝ} (hr : 0 < r) {x v y w : Space}
    (h : Near r x v y w) : Tube r y w ⊆ Wide r x v := by
  obtain ⟨p, hpx, hpy⟩ := h.1
  obtain ⟨a, ha, hpa⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hpx
  obtain ⟨b, hb, hpb⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hpy
  have hdir : min ‖w - v‖ ‖w + v‖ ≤ 100000 * r := by
    simpa only [norm_sub_rev w v, add_comm w v] using h.2.le
  obtain ⟨σ, hσ, hwσ⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_sign hdir
  intro q hq
  obtain ⟨t, ht, hqt⟩ := WangZahlLot.Obl.wz_balanced_cluster_cover.exists_param_of_mem_tube hq
  have htb : |t - b| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, hb.1, hb.2]
  have hpar : |a + (t - b) * σ| ≤ 50 := by
    calc
      |a + (t - b) * σ| ≤ |a| + |t - b| * |σ| := by
        simpa only [abs_mul] using abs_add_le a ((t - b) * σ)
      _ ≤ 1 + 1 * 1 := add_le_add (by rw [abs_of_nonneg ha.1]; exact ha.2)
        (mul_le_mul htb hσ (abs_nonneg _) zero_le_one)
      _ ≤ 50 := by norm_num
  apply WangZahlLot.Obl.wz_separated_cover_refinement.mem_container hpar
  have he : q - (x + (a + (t - b) * σ) • v) =
      (q - (y + t • w)) + (p - (x + a • v)) - (p - (y + b • w)) +
        (t - b) • (w - σ • v) := by module
  rw [he]
  have hsm : ‖(t - b) • (w - σ • v)‖ ≤ 100000 * r := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul htb hwσ (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hn := norm_add_le ((q - (y + t • w)) + (p - (x + a • v)) - (p - (y + b • w)))
    ((t - b) • (w - σ • v))
  have hn' := norm_sub_le ((q - (y + t • w)) + (p - (x + a • v))) (p - (y + b • w))
  have hn'' := norm_add_le (q - (y + t • w)) (p - (x + a • v))
  linarith

lemma wide_volume {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (Wide r x v) ≤ ENNReal.ofReal (200000000000000000000 * r ^ 2) := by
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper
    (x - (50 : ℝ) • v) v hv (T := Icc 0 1) subset_rfl (r := 10000 * r) (A := 1)
    (by positivity) zero_le_one (by
      intro s hs t ht
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
  have he : (fun t : ℝ => x - (50 : ℝ) • v + t • v) '' Icc 0 1 =
      segment ℝ (x - (50 : ℝ) • v) (x - (50 : ℝ) • v + v) := by
    rw [segment_eq_image']
    simp
  rw [he] at h
  unfold Wide WangZahlLot.Obl.wz_separated_cover_refinement.Container
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
  change ENNReal.ofReal (|(100 : ℝ) ^ 3|) * volume (Tube (10 * (1000 * r)) _ _) ≤ _
  rw [show 10 * (1000 * r) = 10000 * r by ring]
  calc
    _ ≤ ENNReal.ofReal (|(100 : ℝ) ^ 3|) *
        ENNReal.ofReal (128 * (2 * 1 + 10000 * r) * (10000 * r) ^ 2) := mul_le_mul' le_rfl h
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      norm_num
      nlinarith [mul_le_mul_of_nonneg_right hr1 (sq_nonneg r)]

end WangZahlLot.Obl.wz_nsp_separated_full_subtree
