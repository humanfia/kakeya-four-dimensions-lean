-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_robust_cluster_estimate.Affine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Geometry

namespace WangZahlLot.Obl.wz_affine_robust_cluster_estimate

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section

/-- Translation, rotation, transverse dilation, and a final uniform contraction. -/
def affine (e : E ≃ₗᵢ[ℝ] E) (a : E) (κ t : ℝ) (hκ : κ ≠ 0) (ht : t ≠ 0) : E ≃ᴬ[ℝ] E :=
  (ContinuousAffineEquiv.vaddConst ℝ (-a)).trans
    ((e.toLinearEquiv.trans (stretchEquiv t ht)).trans
      (LinearEquiv.smulOfNeZero ℝ E κ hκ)).toContinuousLinearEquiv.toContinuousAffineEquiv

@[simp] theorem affine_apply (e : E ≃ₗᵢ[ℝ] E) (a : E) (κ t : ℝ)
    (hκ : κ ≠ 0) (ht : t ≠ 0) (p : E) :
    affine e a κ t hκ ht p = κ • stretch t (e (p - a)) := by
  rfl

theorem volume_rotation (e : E ≃ₗᵢ[ℝ] E) (W : Set E) : volume (e '' W) = volume W := by
  rw [show e '' W = e.symm ⁻¹' W by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hp; exact ⟨e.symm p, hp, e.apply_symm_apply p⟩]
  exact e.symm.measurePreserving.measure_preimage_emb e.symm.toHomeomorph.measurableEmbedding W

theorem volume_affine (e : E ≃ₗᵢ[ℝ] E) (a : E) {κ t : ℝ}
    (hκ : 0 < κ) (ht : 0 < t) (W : Set E) :
    volume (affine e a κ t hκ.ne' ht.ne' '' W) =
      ENNReal.ofReal (κ ^ 3 * t ^ 2) * volume W := by
  have he : affine e a κ t hκ.ne' ht.ne' '' W =
      (κ • stretch t) '' (e '' ((fun p : E => p - a) '' W)) := by
    simp only [image_image]
    rfl
  rw [he, Measure.addHaar_image_linearMap, LinearMap.det_smul,
    finrank_euclideanSpace_fin, det_stretch, abs_of_pos (by positivity), volume_rotation]
  simp only [sub_eq_add_neg, image_add_right, measure_preimage_add_right]

theorem affine_sub (e : E ≃ₗᵢ[ℝ] E) (a : E) (κ t : ℝ)
    (hκ : κ ≠ 0) (ht : t ≠ 0) (p q : E) :
    affine e a κ t hκ ht p - affine e a κ t hκ ht q = κ • stretch t (e (p - q)) := by
  simp only [affine_apply, ← smul_sub, ← map_sub]
  congr 3
  abel

theorem affine_dist_le (e : E ≃ₗᵢ[ℝ] E) (a : E) {κ t : ℝ}
    (hκ : 0 < κ) (ht : 1 ≤ t) (p q : E) :
    dist (affine e a κ t hκ.ne' (by linarith) p)
      (affine e a κ t hκ.ne' (by linarith) q) ≤ κ * t * dist p q := by
  rw [dist_eq_norm, affine_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hκ, dist_eq_norm]
  calc
    κ * ‖stretch t (e (p - q))‖ ≤ κ * (t * ‖e (p - q)‖) := by gcongr; exact norm_stretch_le ht _
    _ = _ := by rw [e.norm_map]; ring

/-- The center of the cluster is sent to the origin; its whole cylinder stays small. -/
theorem affine_cylinder_norm (e : E ≃ₗᵢ[ℝ] E) {z w : E} (hew : e w = axis)
    {κ θ C : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) {p : E}
    (hp : p ∈ thickening (C * θ) (segment ℝ z (z + (6 : ℝ) • w))) :
    ‖affine e (z + (3 : ℝ) • w) κ θ⁻¹ hκ.ne' (inv_ne_zero hθ.ne') p‖ < κ * (C + 3) := by
  have ht : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).mpr hθ1
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hq : ‖affine e (z + (3 : ℝ) • w) κ θ⁻¹ hκ.ne' (inv_ne_zero hθ.ne')
      (z + s • (6 : ℝ) • w)‖ ≤ κ * 3 := by
    rw [affine_apply]
    have heq : z + s • (6 : ℝ) • w - (z + (3 : ℝ) • w) = (6 * s - 3) • w := by module
    rw [heq, map_smul, hew, map_smul, stretch_axis, smul_smul, norm_smul,
      Real.norm_eq_abs, norm_axis, mul_one, abs_mul, abs_of_pos hκ]
    have : |6 * s - 3| ≤ 3 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    gcongr
  have hd := affine_dist_le e (z + (3 : ℝ) • w) hκ ht p (z + s • (6 : ℝ) • w)
  have hdist : κ * θ⁻¹ * dist p (z + s • (6 : ℝ) • w) < κ * C := by
    calc
      κ * θ⁻¹ * dist p (z + s • (6 : ℝ) • w) < κ * θ⁻¹ * (C * θ) := by gcongr
      _ = κ * C := by field_simp
  have hn := norm_le_norm_add_norm_sub
    (affine e (z + (3 : ℝ) • w) κ θ⁻¹ hκ.ne' (inv_ne_zero hθ.ne') (z + s • (6 : ℝ) • w))
    (affine e (z + (3 : ℝ) • w) κ θ⁻¹ hκ.ne' (inv_ne_zero hθ.ne') p)
  rw [norm_sub_rev] at hn
  rw [dist_eq_norm] at hd
  nlinarith only [hn, hd, hq, hdist]

end
end WangZahlLot.Obl.wz_affine_robust_cluster_estimate
