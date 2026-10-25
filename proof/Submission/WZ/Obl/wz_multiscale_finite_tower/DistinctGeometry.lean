-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.DistinctGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic
import Submission.WZ.Obl.wz_transverse_stem_deletion.Geometry

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal
open WangZahlLot.Obl.wz_balanced_cluster_cover (exists_param_of_mem_tube exists_sign)

/-- At sufficiently small radius, separated directions guarantee essential distinctness. -/
lemma half_overlap_of_angle {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1 / 1024)
    {x v y w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hang : 16384 * d ≤ min ‖v - w‖ ‖v + w‖) :
    volume (Tube d x v ∩ Tube d y w) ≤ (1 / 2 : ℝ≥0∞) * volume (Tube d x v) := by
  have hs : segment ℝ y (y + w) ⊆ Set.range (fun t : ℝ => y + t • w) := by
    intro p hp
    rw [segment_eq_image'] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact ⟨t, by simp⟩
  have hsub := Metric.thickening_subset_of_subset d hs
  have hvol := WangZahlLot.Obl.wz_transverse_stem_deletion.tube_line_intersection_volume_le (x := x) (y := y)
    hd hd (by positivity : 0 < 16384 * d) hv hw hang
  have he : 8 * (d + d) / (16384 * d) = (1 / 1024 : ℝ) := by field_simp; ring
  calc
    volume (Tube d x v ∩ Tube d y w) ≤
        volume (Tube d x v ∩ Metric.thickening d (Set.range (fun t : ℝ => y + t • w))) :=
      measure_mono (Set.inter_subset_inter_right _ hsub)
    _ ≤ ENNReal.ofReal (128 * (8 * (d + d) / (16384 * d) + d) * d ^ 2) := hvol
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * d ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      rw [he]
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg d)
    _ = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (d ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ ≤ (1 / 2 : ℝ≥0∞) * volume (Tube d x v) :=
      mul_le_mul' le_rfl (WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hd x v hv)

lemma angle_le_of_large_overlap {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1 / 1024)
    {x v y w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hover : ¬volume (Tube d x v ∩ Tube d y w) ≤ (1 / 2 : ℝ≥0∞) * volume (Tube d x v)) :
    min ‖v - w‖ ‖v + w‖ ≤ 16384 * d := by
  by_contra h
  exact hover (half_overlap_of_angle hd hd1 hv hw (le_of_lt (lt_of_not_ge h)))

/-- A fixed enlarged cylinder containing all near-parallel tubes meeting a fixed tube. -/
def OverlapContainer (d : ℝ) (x v : Space) : Set Space :=
  AffineMap.homothety (x - v) (3 : ℝ) '' Tube (20000 * d) (x - v) v

lemma mem_overlapContainer {d : ℝ} (hd : 0 < d) {x v p : Space} {t : ℝ}
    (ht : -1 ≤ t ∧ t ≤ 2) (hp : ‖p - (x + t • v)‖ < 20000 * d) :
    p ∈ OverlapContainer d x v := by
  let b := x - v
  let q := b + (1 / 3 : ℝ) • (p - b)
  have hq : q ∈ Tube (20000 * d) b v := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨b + ((t + 1) / 3) • v, ?_, ?_⟩
    · rw [segment_eq_image']
      refine ⟨(t + 1) / 3, ⟨by linarith [ht.1], by linarith [ht.2]⟩, by simp⟩
    · rw [dist_eq_norm]
      have he : q - (b + ((t + 1) / 3) • v) = (1 / 3 : ℝ) • (p - (x + t • v)) := by
        dsimp [q, b]
        module
      rw [he, norm_smul, Real.norm_eq_abs]
      norm_num
      linarith
  refine ⟨q, hq, ?_⟩
  rw [AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  dsimp [q, b]
  module

lemma near_intersecting_tube_subset {d : ℝ} (hd : 0 < d) {x v y w : Space}
    (hang : min ‖w - v‖ ‖w + v‖ ≤ 16384 * d)
    (hinter : (Tube d x v ∩ Tube d y w).Nonempty) : Tube d y w ⊆ OverlapContainer d x v := by
  obtain ⟨p, hpx, hpy⟩ := hinter
  obtain ⟨a, ha, hpa⟩ := exists_param_of_mem_tube hpx
  obtain ⟨b, hb, hpb⟩ := exists_param_of_mem_tube hpy
  obtain ⟨z, hz, hwz⟩ := exists_sign hang
  intro q hq
  obtain ⟨t, ht, hqt⟩ := exists_param_of_mem_tube hq
  have htb : |t - b| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1, hb.2], by linarith [ht.2, hb.1]⟩
  have htz : |(t - b) * z| ≤ 1 := by
    rw [abs_mul]
    have h := mul_le_mul htb hz (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hpar : -1 ≤ a + (t - b) * z ∧ a + (t - b) * z ≤ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp htz
    constructor <;> linarith [ha.1, ha.2]
  apply mem_overlapContainer hd hpar
  have he : q - (x + (a + (t - b) * z) • v) =
      (q - (y + t • w)) + (p - (x + a • v)) - (p - (y + b • w)) +
        (t - b) • (w - z • v) := by module
  have hlast : ‖(t - b) • (w - z • v)‖ ≤ 16384 * d := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |t - b| * ‖w - z • v‖ ≤ 1 * (16384 * d) := mul_le_mul htb hwz (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  rw [he]
  calc
    _ ≤ (‖q - (y + t • w)‖ + ‖p - (x + a • v)‖) + ‖p - (y + b • w)‖ +
        ‖(t - b) • (w - z • v)‖ := by
      apply (norm_add_le _ _).trans
      gcongr
      exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < 20000 * d := by linarith

lemma overlapContainer_volume {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1 / 100000)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (OverlapContainer d x v) ≤ ENNReal.ofReal (10000000000000 * d ^ 2) := by
  have ht := WangZahlLot.Obl.wz_balanced_cluster_cover.tube_volume_le
    (by positivity : 0 < 20000 * d) (by linarith : 20000 * d ≤ 1) (x - v) v hv
  rw [OverlapContainer, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
  calc
    _ ≤ ENNReal.ofReal (|(3 : ℝ) ^ 3|) * ENNReal.ofReal (384 * (20000 * d) ^ 2) :=
      mul_le_mul' le_rfl ht
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      norm_num
      nlinarith [sq_nonneg d]

end WangZahlLot.Obl.wz_multiscale_finite_tower
