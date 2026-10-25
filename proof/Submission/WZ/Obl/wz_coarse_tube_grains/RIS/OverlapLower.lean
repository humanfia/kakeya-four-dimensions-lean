-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.OverlapLower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RecoverEstimate
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Small transverse and angular perturbations, with a fixed small longitudinal
shift, contain the central contraction of the first capsule. -/
theorem contracted_tube_subset_nearby {δ : ℝ} (hδ : 0 < δ)
    {x v y w : Space} {s : ℝ} (hs : |s| ≤ 1 / 100)
    (hpos : ‖y - (x + s • v)‖ ≤ δ / 100)
    (hdir : ‖v - w‖ ≤ δ / 100) :
    AffineMap.homothety (x + (1 / 2 : ℝ) • v) (9 / 10 : ℝ) '' Tube δ x v ⊆
      Tube δ y w := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨z, hz, hqz⟩ := mem_thickening_iff.mp hq
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [add_sub_cancel_left] at hqz
  let a : ℝ := (1 / 20 : ℝ) + (9 / 10 : ℝ) * t
  have hs' := abs_le.mp hs
  have ha : a - s ∈ Icc (0 : ℝ) 1 := by
    dsimp [a]
    constructor <;> linarith [ht.1, ht.2, hs'.1, hs'.2]
  apply mem_thickening_iff.mpr
  refine ⟨y + (a - s) • w, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨a - s, ha, by simp⟩
  · rw [dist_eq_norm]
    have heq : AffineMap.homothety (x + (1 / 2 : ℝ) • v) (9 / 10 : ℝ) q -
          (y + (a - s) • w) =
        (9 / 10 : ℝ) • (q - (x + t • v)) - (y - (x + s • v)) +
          (a - s) • (v - w) := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      dsimp [a]
      module
    have hrad : ‖(9 / 10 : ℝ) • (q - (x + t • v))‖ < (9 / 10 : ℝ) * δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 10)]
      exact mul_lt_mul_of_pos_left hqz (by norm_num)
    have hang : ‖(a - s) • (v - w)‖ ≤ δ / 100 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
      exact (mul_le_mul ha.2 hdir (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    rw [heq]
    have htri := norm_sub_le ((9 / 10 : ℝ) • (q - (x + t • v))) (y - (x + s • v))
    have htri' := norm_add_le
      ((9 / 10 : ℝ) • (q - (x + t • v)) - (y - (x + s • v))) ((a - s) • (v - w))
    linarith

/-- Nearby capsule parameters force more than half-volume overlap. The proof
uses the exact volume of a homothety, without computing the capsule volume. -/
theorem intersection_gt_half_of_near_parameters {δ : ℝ} (hδ : 0 < δ)
    {x v y w : Space} (hv : ‖v‖ = 1) {s : ℝ} (hs : |s| ≤ 1 / 100)
    (hpos : ‖y - (x + s • v)‖ ≤ δ / 100)
    (hdir : ‖v - w‖ ≤ δ / 100) :
    (1 / 2 : ENNReal) * volume (Tube δ x v) < volume (Tube δ x v ∩ Tube δ y w) := by
  let H := AffineMap.homothety (x + (1 / 2 : ℝ) • v) (9 / 10 : ℝ)
  have hfirst : H '' Tube δ x v ⊆ Tube δ x v := by
    exact contracted_tube_subset_nearby hδ (s := 0) (by norm_num)
      (by simpa using (show (0 : ℝ) ≤ δ / 100 by positivity))
      (by simpa using (show (0 : ℝ) ≤ δ / 100 by positivity))
  have hsecond : H '' Tube δ x v ⊆ Tube δ y w :=
    contracted_tube_subset_nearby hδ hs hpos hdir
  have hmeasure : volume (H '' Tube δ x v) =
      ENNReal.ofReal ((9 / 10 : ℝ) ^ 3) * volume (Tube δ x v) := by
    dsimp only [H]
    rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
    norm_num
  have hvol : 0 < volume (Tube δ x v) :=
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hδ)).trans_le
      (wz_direction_density_transfer.tube_volume_lower hδ x v hv)
  calc
    (1 / 2 : ENNReal) * volume (Tube δ x v) <
        ENNReal.ofReal ((9 / 10 : ℝ) ^ 3) * volume (Tube δ x v) := by
      rw [mul_comm (1 / 2 : ENNReal), mul_comm (ENNReal.ofReal ((9 / 10 : ℝ) ^ 3))]
      apply ENNReal.mul_lt_mul_right hvol.ne' (tube_volume_ne_top δ x v)
      have he : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [he]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
    _ = volume (H '' Tube δ x v) := hmeasure.symm
    _ ≤ volume (Tube δ x v ∩ Tube δ y w) :=
      measure_mono (subset_inter hfirst hsecond)

/-- Essential distinctness therefore separates at least one of the transverse
position and direction parameters, for any fixed small longitudinal shift. -/
theorem separation_of_half_intersection {δ : ℝ} (hδ : 0 < δ)
    {x v y w : Space} (hv : ‖v‖ = 1)
    (hhalf : volume (Tube δ x v ∩ Tube δ y w) ≤ (1 / 2 : ENNReal) * volume (Tube δ x v))
    {s : ℝ} (hs : |s| ≤ 1 / 100) :
    δ / 100 < ‖y - (x + s • v)‖ ∨ δ / 100 < ‖v - w‖ := by
  by_contra h
  push Not at h
  exact (intersection_gt_half_of_near_parameters hδ hv hs h.1 h.2).not_ge hhalf

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
