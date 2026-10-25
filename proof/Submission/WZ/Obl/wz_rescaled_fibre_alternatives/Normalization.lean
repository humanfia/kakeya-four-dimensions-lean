-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Normalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.AffineSlabs
import Submission.WZ.Obl.wz_nonflat_factored_improvement

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate
  (affine affine_apply affine_dist_le affine_sub volume_affine stretch stretch_axis axis norm_axis)

noncomputable section

abbrev contraction : ℝ := 1 / 100000000

abbrev normalizedRadius (r s : ℝ) : ℝ := 4 * (contraction * r⁻¹ * s)
abbrev jacobian (r : ℝ) : ℝ := contraction ^ 3 * r⁻¹ ^ 2
abbrev fiberVolume : ℝ := 896 / contraction

/-- Normalize a parent tube by expanding only the two transverse directions. -/
def normalize (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) (r : ℝ) (hr : 0 < r) :
    Space ≃ᴬ[ℝ] Space :=
  affine e (y + (1 / 2 : ℝ) • w) contraction r⁻¹ (by norm_num) (inv_ne_zero hr.ne')

lemma normalize_volume (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {r : ℝ} (hr : 0 < r)
    (U : Set Space) : volume (normalize e y w r hr '' U) =
      ENNReal.ofReal (jacobian r) * volume U :=
  volume_affine e _ (by norm_num) (inv_pos.mpr hr) U

lemma normalize_dist (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (p q : Space) :
    dist (normalize e y w r hr p) (normalize e y w r hr q) ≤
      (contraction * r⁻¹) * dist p q :=
  affine_dist_le e _ (by norm_num) ((one_le_inv₀ hr).mpr hr1) p q

lemma normalize_doubled_norm (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {p : Space}
    (hp : p ∈ doubled r y w) : ‖normalize e y w r hr p‖ < 3 * contraction := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have he : y - (1 / 2 : ℝ) • w + t • (2 • w) - (y + (1 / 2 : ℝ) • w) =
      (2 * t - 1) • w := by module
  have hq : ‖normalize e y w r hr (y - (1 / 2 : ℝ) • w + t • (2 • w))‖ ≤ contraction := by
    simp only [normalize, affine_apply, he, map_smul, hew, stretch_axis,
      smul_smul, norm_smul, Real.norm_eq_abs, norm_axis, mul_one, abs_mul]
    rw [abs_of_pos (by norm_num : 0 < contraction)]
    have ht' : |2 * t - 1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa using mul_le_mul_of_nonneg_left ht' (by norm_num : 0 ≤ contraction)
  have hd := normalize_dist e y w hr hr1 p (y - (1 / 2 : ℝ) • w + t • (2 • w))
  have hdist : dist (normalize e y w r hr p)
      (normalize e y w r hr (y - (1 / 2 : ℝ) • w + t • (2 • w))) < 2 * contraction := by
    have he' : contraction * r⁻¹ * (2 * r) = 2 * contraction := by field_simp
    exact hd.trans_lt (he' ▸ mul_lt_mul_of_pos_left hpq (by positivity))
  have hn := norm_le_norm_add_norm_sub
    (normalize e y w r hr (y - (1 / 2 : ℝ) • w + t • (2 • w)))
    (normalize e y w r hr p)
  rw [norm_sub_rev, ← dist_eq_norm] at hn
  dsimp [contraction] at hq hdist ⊢
  linarith only [hq, hdist, hn]

lemma normalize_parent_norm (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {p : Space}
    (hp : p ∈ tube r y w) : ‖normalize e y w r hr p‖ < 3 * contraction :=
  normalize_doubled_norm e hew hr hr1 (tube_subset_doubled hr.le y w hp)

lemma normalize_doubled_subset_ball (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    normalize e y w r hr '' doubled r y w ⊆ ball (0 : Space) 1 := by
  rintro _ ⟨p, hp, rfl⟩
  rw [mem_ball_zero_iff]
  exact (normalize_doubled_norm e hew hr hr1 hp).trans (by norm_num)

lemma normalize_doubled_volume_lower (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hw : ‖w‖ = 1) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (contraction ^ 3) ≤ volume (normalize e y w r hr '' doubled r y w) := by
  rw [normalize_volume]
  have hlow := WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hr y w hw
  have hh := hlow.trans (measure_mono (tube_subset_doubled hr.le y w))
  calc
    _ = ENNReal.ofReal (jacobian r) * ENNReal.ofReal (r ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [jacobian]
      field_simp
    _ ≤ _ := mul_le_mul_right hh _

lemma normalizedRadius_pos {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 < normalizedRadius r s := by unfold normalizedRadius contraction; positivity

lemma normalizedRadius_le {r s : ℝ} (hr : 0 < r) (hsr : s ≤ r) :
    normalizedRadius r s ≤ 4 * contraction := by
  have h := mul_le_mul_of_nonneg_left hsr (by positivity : 0 ≤ 4 * contraction * r⁻¹)
  have he : 4 * contraction * r⁻¹ * r = 4 * contraction := by field_simp
  rw [he] at h
  simpa only [normalizedRadius, mul_assoc] using h

/-- The affine image of a child fits into a tiny prism centered at its midpoint. -/
lemma normalize_child_prism (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {r s : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 < s) (hsr : s ≤ r) (x v : Space) (hv : ‖v‖ = 1)
    (hT : tube s x v ⊆ tube r y w) :
    ‖normalize e y w r hr (x + (1 / 2 : ℝ) • v)‖ < 1 / 100 ∧
    ∃ u : Fin 3 → Space, Orthonormal ℝ u ∧
      normalize e y w r hr '' tube s x v ⊆
        WangZahlLot.Obl.wz_transverse_cell_weighted_cover.prism
          (contraction * r⁻¹ * s) (contraction * r⁻¹ * s)
          (normalize e y w r hr (x + (1 / 2 : ℝ) • v)) u := by
  have hseg : segment ℝ x (x + v) ⊆ tube r y w :=
    (self_subset_thickening hs _).trans hT
  have hmid : x + (1 / 2 : ℝ) • v ∈ segment ℝ x (x + v) := by
    rw [segment_eq_image']
    exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, by simp⟩
  refine ⟨(normalize_parent_norm e hew hr hr1 (hseg hmid)).trans (by norm_num), ?_⟩
  apply WangZahlLot.Obl.wz_nonflat_factored_improvement.affine_tube_prism
    (normalize e y w r hr).toAffineEquiv (by positivity)
    (by have h := normalizedRadius_le hr hsr; dsimp [normalizedRadius, contraction] at h ⊢; linarith)
    (normalize_dist e y w hr hr1) x v hv
  have h0 := normalize_parent_norm e hew hr hr1 (hseg (left_mem_segment ℝ x (x + v)))
  have h1 := normalize_parent_norm e hew hr hr1 (hseg (right_mem_segment ℝ x (x + v)))
  have he : (normalize e y w r hr).toAffineEquiv.linear v =
      normalize e y w r hr (x + v) - normalize e y w r hr x := by
    have he := (normalize e y w r hr).toAffineEquiv.map_vadd x v
    convert eq_sub_iff_add_eq.mpr he.symm using 1 <;> simp only [vadd_eq_add, add_comm] <;> rfl
  rw [he]
  have hn := norm_sub_le (normalize e y w r hr (x + v)) (normalize e y w r hr x)
  dsimp [contraction] at h0 h1
  linarith

lemma normalize_preimage_tube_volume (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r) (z u : Space) (hu : ‖u‖ = 1) :
    volume (normalize e y w r hr ⁻¹' tube (normalizedRadius r s) z u) ≤
      ENNReal.ofReal (fiberVolume * s ^ 2) := by
  have hpre := WangZahlLot.Obl.wz_nonflat_factored_improvement.affine_volume_preimage
    (normalize e y w r hr).toAffineEquiv (by positivity : 0 < jacobian r)
    (normalize_volume e y w hr) (tube (normalizedRadius r s) z u)
  change volume ((normalize e y w r hr).toAffineEquiv ⁻¹' tube (normalizedRadius r s) z u) ≤ _
  rw [hpre]
  calc
    _ ≤ ENNReal.ofReal (jacobian r)⁻¹ * ENNReal.ofReal (56 * (normalizedRadius r s) ^ 2) := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity)]
      exact mul_le_mul_right
        (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper
          (normalizedRadius_pos hr hs).le ((normalizedRadius_le hr hsr).trans (by norm_num)) z u hu) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [jacobian, normalizedRadius, fiberVolume]
      field_simp
      ring

end
end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
