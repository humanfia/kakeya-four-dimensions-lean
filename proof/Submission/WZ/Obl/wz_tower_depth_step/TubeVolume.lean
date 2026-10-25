-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_depth_step.TubeVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_depth_step.CountTransport

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_depth_step

open Set Metric MeasureTheory Module

lemma tube_image_add (r : ℝ) (x v z : Space) :
    (fun p => p + z) '' Tube r x v = Tube r (x + z) v := by
  have hshift {x v z p : Space} (hp : p ∈ Tube r x v) : p + z ∈ Tube r (x + z) v := by
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
    rw [segment_eq_image'] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    apply mem_thickening_iff.mpr
    refine ⟨x + z + t • v, ?_, ?_⟩
    · rw [segment_eq_image']
      exact ⟨t, ht, by simp⟩
    · rw [dist_eq_norm] at hpq ⊢
      convert hpq using 1
      congr 1
      module
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hshift hq
  · intro hp
    refine ⟨p - z, ?_, by simp⟩
    have hh := hshift (z := -z) hp
    simpa [sub_eq_add_neg] using hh

lemma tube_volume_translate (r : ℝ) (x v z : Space) :
    volume (Tube r (x + z) v) = volume (Tube r x v) := by
  rw [← tube_image_add, image_add_right, measure_preimage_add_right]

/-- Radius enlargement is bounded by the volume of a homothetic enlargement. -/
lemma tube_volume_enlarge {r E : ℝ} (_hr : 0 < r) (hE : 1 ≤ E) (x v : Space) :
    volume (Tube (E * r) x v) ≤ ENNReal.ofReal (E ^ 3) * volume (Tube r x v) := by
  have hEp : 0 < E := by linarith
  have hi : 0 < E⁻¹ := inv_pos.mpr hEp
  have hi1 : E⁻¹ ≤ 1 := (inv_le_one₀ hEp).mpr hE
  let m := x + (1 / 2 : ℝ) • v
  have hsub : Tube (E * r) x v ⊆ AffineMap.homothety m E '' Tube r x v := by
    intro p hp
    obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.mp hp
    rw [segment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    simp only [add_sub_cancel_left] at hpz
    let q := AffineMap.homothety m E⁻¹ p
    let z := x + ((1 - E⁻¹) / 2 + E⁻¹ * t) • v
    have hzseg : z ∈ segment ℝ x (x + v) := by
      rw [segment_eq_image']
      refine ⟨(1 - E⁻¹) / 2 + E⁻¹ * t, ⟨?_, ?_⟩, by simp [z]⟩
      · exact add_nonneg (div_nonneg (sub_nonneg.mpr hi1) (by norm_num)) (mul_nonneg hi.le ht.1)
      · nlinarith [mul_le_mul_of_nonneg_left ht.2 hi.le]
    have hzmap : z = AffineMap.homothety m E⁻¹ (x + t • v) := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
      dsimp [z, m]
      module
    have hq : q ∈ Tube r x v := by
      apply mem_thickening_iff.mpr
      refine ⟨z, hzseg, ?_⟩
      rw [hzmap]
      change dist (AffineMap.homothety m E⁻¹ p) (AffineMap.homothety m E⁻¹ (x + t • v)) < r
      rw [dist_homothety, Real.norm_eq_abs, abs_of_pos hi]
      calc
        _ < E⁻¹ * (E * r) := mul_lt_mul_of_pos_left hpz hi
        _ = r := by rw [← mul_assoc, inv_mul_cancel₀ hEp.ne', one_mul]
    refine ⟨q, hq, ?_⟩
    dsimp [q]
    rw [← AffineMap.homothety_mul_apply, mul_inv_cancel₀ hEp.ne', AffineMap.homothety_one]
    rfl
  calc
    _ ≤ volume (AffineMap.homothety m E '' Tube r x v) := measure_mono hsub
    _ = _ := by rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin, abs_of_pos (by positivity)]

lemma tube_volume_ne_zero {r : ℝ} (hr : 0 < r) (x v : Space) :
    volume (Tube r x v) ≠ 0 := by
  apply ne_of_gt
  exact (measure_ball_pos volume x hr).trans_le
    (measure_mono (ball_subset_thickening (left_mem_segment ℝ x (x + v)) r))

lemma tube_volume_ne_top (r : ℝ) (x v : Space) : volume (Tube r x v) ≠ ⊤ := by
  have hc : IsCompact (segment ℝ x (x + v)) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  exact hc.isBounded.thickening.measure_lt_top.ne

end WangZahlLot.Obl.wz_tower_depth_step
