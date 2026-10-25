-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.TubeGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.TubeBodies

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric

/-- Similarities act exactly on the open tube convention in the frozen statement. -/
lemma similarity_tube_image (f : Space ≃ᵃ[ℝ] Space) {t : ℝ} (ht : 0 < t)
    (hscale : ∀ p q, dist (f p) (f q) = t * dist p q)
    (δ : ℝ) (x v : Space) :
    f '' Tube δ x v = Tube (t * δ) (f x) (f.linear v) := by
  have hmap : f (x + v) = f x + f.linear v := by
    simpa only [vadd_eq_add, add_comm] using f.map_vadd x v
  have hseg : f '' segment ℝ x (x + v) = segment ℝ (f x) (f x + f.linear v) := by
    have hh := image_segment ℝ f.toAffineMap x (x + v)
    change f '' segment ℝ x (x + v) = segment ℝ (f x) (f (x + v)) at hh
    rwa [hmap] at hh
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨r, hr, hqr⟩ := mem_thickening_iff.mp hq
    refine mem_thickening_iff.mpr ⟨f r, ?_, ?_⟩
    · rw [← hseg]
      exact ⟨r, hr, rfl⟩
    · rw [hscale]
      exact mul_lt_mul_of_pos_left hqr ht
  · intro hp
    obtain ⟨r, hr, hpr⟩ := mem_thickening_iff.mp hp
    rw [← hseg] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    refine ⟨f.symm p, mem_thickening_iff.mpr ⟨q, hq, ?_⟩, f.apply_symm_apply p⟩
    have hh := hscale (f.symm p) q
    rw [f.apply_symm_apply] at hh
    rw [hh] at hpr
    exact (mul_lt_mul_iff_right₀ ht).mp hpr

noncomputable def dilation (p : Space) (t : ℝ) (ht : t ≠ 0) : Space ≃ᵃ[ℝ] Space :=
  (AffineEquiv.vaddConst ℝ p).symm.trans
    ((LinearEquiv.smulOfNeZero ℝ Space t ht).toAffineEquiv.trans (AffineEquiv.vaddConst ℝ p))

@[simp] lemma dilation_apply (p : Space) (t : ℝ) (ht : t ≠ 0) (q : Space) :
    dilation p t ht q = t • (q - p) + p := rfl

@[simp] lemma dilation_linear (p : Space) (t : ℝ) (ht : t ≠ 0) (v : Space) :
    (dilation p t ht).linear v = t • v := by
  have hh := (dilation p t ht).toAffineMap.linearMap_vsub v 0
  change (dilation p t ht).linear (v - 0) = dilation p t ht v - dilation p t ht 0 at hh
  rw [sub_zero] at hh
  rw [hh, dilation_apply, dilation_apply]
  module

lemma dilation_dist (p : Space) {t : ℝ} (ht : 0 < t) (q r : Space) :
    dist (dilation p t ht.ne' q) (dilation p t ht.ne' r) = t * dist q r := by
  rw [dilation_apply, dilation_apply, dist_add_right, dist_eq_norm]
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rfl

lemma dilation_tube_image (p : Space) {t : ℝ} (ht : 0 < t) (δ : ℝ) (x v : Space) :
    dilation p t ht.ne' '' Tube δ x v =
      Tube (t * δ) (dilation p t ht.ne' x) (t • v) := by
  simpa only [dilation_linear] using
    similarity_tube_image (dilation p t ht.ne') ht (dilation_dist p ht) δ x v

lemma doubled_tube_image (ρ : ℝ) (y w : Space) :
    Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w) =
      dilation (y + (1 / 2 : ℝ) • w) 2 (by norm_num) '' Tube ρ y w := by
  rw [dilation_tube_image _ (by norm_num : (0 : ℝ) < 2)]
  congr 1
  · rw [dilation_apply]
    module
  · simp [two_smul]

lemma doubled_tube_volume (ρ : ℝ) (y w : Space) :
    volume (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w)) = 8 * volume (Tube ρ y w) := by
  rw [doubled_tube_image]
  change volume (AffineMap.homothety (y + (1 / 2 : ℝ) • w) (2 : ℝ) '' Tube ρ y w) = _
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
  norm_num

lemma doubled_closed_volume_bounds {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (y w : Space) (hw : ‖w‖ = 1) :
    ENNReal.ofReal (8 * ρ ^ 2) ≤
        volume (closure (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w))) ∧
      volume (closure (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w))) ≤
        ENNReal.ofReal (3072 * ρ ^ 2) := by
  rw [show volume (closure (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w))) =
      volume (Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w)) from
    WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_closedTube _ _ _, doubled_tube_volume]
  obtain ⟨hl, hu⟩ := WangZahlLot.Obl.wz_regular_transverse_affine_cells.closedTube_volume_bounds
    hρ hρ1 y w hw
  rw [WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_closedTube] at hl hu
  change ENNReal.ofReal (ρ ^ 2) ≤ volume (Tube ρ y w) at hl
  change volume (Tube ρ y w) ≤ ENNReal.ofReal (384 * ρ ^ 2) at hu
  constructor
  · simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_ofNat] using
      mul_le_mul' (le_rfl : (8 : ENNReal) ≤ 8) hl
  · calc
      _ ≤ (8 : ENNReal) * ENNReal.ofReal (384 * ρ ^ 2) := mul_le_mul' le_rfl hu
      _ = _ := by
        rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
        congr 1
        ring

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
