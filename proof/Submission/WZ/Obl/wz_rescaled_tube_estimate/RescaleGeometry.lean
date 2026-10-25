-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_tube_estimate.RescaleGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_tube_estimate.StretchSeparation
import Submission.WZ.Obl.wz_rescaled_tube_estimate.ParameterPacking
import Submission.WZ.Obl.wz_rescaled_tube_estimate.ClusterGeometry
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Affine
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Tubes
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Transport

/-!
# Geometry of the anisotropic rescaling of a `ρ`-tube

A `δ`-tube inside the `ρ`-tube `Tube ρ y w` points within `4ρ` of `±w`. After rotating `w` to
the first coordinate axis, moving the centre `y + w/2` to the origin, stretching the two
transverse coordinates by `ρ⁻¹` and contracting by `κ`, its image lies in an exact unit tube of
radius `κ ρ⁻¹ δ` centred within `3κ/2` of the origin.
-/

namespace WangZahlLot.Obl.wz_rescaled_tube_estimate

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_affine_robust_cluster_estimate

noncomputable section

/-- A unit tube inside a fatter unit tube points within `4ρ` of the fatter tube's direction,
up to sign. -/
theorem pd_lt_of_tube_subset {δ ρ : ℝ} (hδ : 0 < δ) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (h : Tube δ x v ⊆ Tube ρ y w) :
    pd v w < 4 * ρ := by
  have hx : x ∈ Tube ρ y w :=
    h (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hxv : x + v ∈ Tube ρ y w :=
    h (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  obtain ⟨q, hq, hxq⟩ := mem_thickening_iff.mp hx
  obtain ⟨q', hq', hxq'⟩ := mem_thickening_iff.mp hxv
  rw [segment_eq_image'] at hq hq'
  obtain ⟨s, hs, rfl⟩ := hq
  obtain ⟨s', hs', rfl⟩ := hq'
  simp only [add_sub_cancel_left] at hxq hxq'
  rw [dist_eq_norm] at hxq hxq'
  set d := s' - s with hd_def
  have hdv : ‖v - d • w‖ < 2 * ρ := by
    have heq : v - d • w = (x + v - (y + s' • w)) - (x - (y + s • w)) := by
      rw [hd_def]; module
    rw [heq]
    have := norm_sub_le (x + v - (y + s' • w)) (x - (y + s • w))
    linarith
  have hdw : ‖d • w‖ = |d| := by rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
  have hgap : 1 - |d| < 2 * ρ := by
    have := norm_sub_norm_le v (d • w)
    rw [hv, hdw] at this
    linarith
  have hd1 : |d| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1, hs.2, hs'.1, hs'.2],
    by linarith [hs.1, hs.2, hs'.1, hs'.2]⟩
  rcases le_or_gt 0 d with hd0 | hd0
  · have habs : |d| = d := abs_of_nonneg hd0
    have hsub : ‖v - w‖ < 4 * ρ := by
      have heq : v - w = (v - d • w) - (1 - d) • w := by module
      rw [heq]
      have h1 := norm_sub_le (v - d • w) ((1 - d) • w)
      rw [norm_smul, Real.norm_eq_abs, hw, mul_one,
        abs_of_nonneg (by linarith [habs ▸ hd1] : (0 : ℝ) ≤ 1 - d)] at h1
      linarith
    exact (min_le_left _ _).trans_lt hsub
  · have habs : |d| = -d := abs_of_neg hd0
    have hadd : ‖v + w‖ < 4 * ρ := by
      have heq : v + w = (v - d • w) + (1 + d) • w := by module
      rw [heq]
      have h1 := norm_add_le (v - d • w) ((1 + d) • w)
      rw [norm_smul, Real.norm_eq_abs, hw, mul_one,
        abs_of_nonneg (by linarith [habs ▸ hd1] : (0 : ℝ) ≤ 1 + d)] at h1
      linarith
    exact (min_le_right _ _).trans_lt hadd

/-- The rescaling map attached to the `ρ`-tube `Tube ρ y w`, given a rotation `e` with
`e w = axis`. -/
def rescaleMap (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) :
    Space ≃ᴬ[ℝ] Space :=
  affine e (y + (1 / 2 : ℝ) • w) κ ρ⁻¹ hκ.ne' (inv_ne_zero hρ.ne')

theorem rescaleMap_apply (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (p : Space) :
    rescaleMap e y w hκ hρ p = κ • stretch ρ⁻¹ (e (p - (y + (1 / 2 : ℝ) • w))) := rfl

theorem rescaleMap_sub (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (p q : Space) :
    rescaleMap e y w hκ hρ p - rescaleMap e y w hκ hρ q = κ • stretch ρ⁻¹ (e (p - q)) :=
  affine_sub _ _ _ _ _ _ p q

theorem rescaleMap_dist_le (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p q : Space) :
    dist (rescaleMap e y w hκ hρ p) (rescaleMap e y w hκ hρ q) ≤ κ * ρ⁻¹ * dist p q :=
  affine_dist_le e _ hκ ((one_le_inv₀ hρ).mpr hρ1) p q

theorem rescaleMap_volume (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (W : Set Space) :
    volume (rescaleMap e y w hκ hρ '' W) = ENNReal.ofReal (κ ^ 3 * (ρ⁻¹) ^ 2) * volume W :=
  volume_affine e _ hκ (inv_pos.mpr hρ) W

/-- Points of the axis segment of the `ρ`-tube go to the first coordinate axis. -/
theorem rescaleMap_segment_norm (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space} (hew : e w = axis)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (s : ℝ) :
    ‖rescaleMap e y w hκ hρ (y + s • w)‖ = κ * |s - 1 / 2| := by
  rw [rescaleMap_apply]
  have heq : y + s • w - (y + (1 / 2 : ℝ) • w) = (s - 1 / 2) • w := by module
  rw [heq, map_smul, hew, map_smul, stretch_axis, smul_smul, norm_smul, Real.norm_eq_abs,
    norm_axis, mul_one, abs_mul, abs_of_pos hκ]

/-- The whole `ρ`-tube is sent into the ball of radius `3κ/2`. -/
theorem rescaleMap_tube_norm_lt (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space} (hew : e w = axis)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {p : Space} (hp : p ∈ Tube ρ y w) :
    ‖rescaleMap e y w hκ hρ p‖ < κ * (3 / 2) := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hq : ‖rescaleMap e y w hκ hρ (y + s • w)‖ ≤ κ * (1 / 2) := by
    rw [rescaleMap_segment_norm e hew hκ hρ]
    have : |s - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    gcongr
  have hd := rescaleMap_dist_le e y w hκ hρ hρ1 p (y + s • w)
  have hdist : κ * ρ⁻¹ * dist p (y + s • w) < κ := by
    calc
      κ * ρ⁻¹ * dist p (y + s • w) < κ * ρ⁻¹ * ρ := by gcongr
      _ = κ := by field_simp
  have hn := norm_le_norm_add_norm_sub (rescaleMap e y w hκ hρ (y + s • w))
    (rescaleMap e y w hκ hρ p)
  rw [norm_sub_rev, ← dist_eq_norm] at hn
  linarith

/-- The two-fold dilate of the `ρ`-tube is sent into the ball of radius `3κ`. -/
theorem rescaleMap_dilate_norm_lt (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space} (hew : e w = axis)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {p : Space}
    (hp : p ∈ Tube (2 * ρ) (y - (1 / 2 : ℝ) • w) (2 • w)) :
    ‖rescaleMap e y w hκ hρ p‖ < κ * 3 := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hqe : y - (1 / 2 : ℝ) • w + s • (2 • w) = y + (2 * s - 1 / 2) • w := by
    rw [two_smul]; module
  have hq : ‖rescaleMap e y w hκ hρ (y - (1 / 2 : ℝ) • w + s • (2 • w))‖ ≤ κ * 1 := by
    rw [hqe, rescaleMap_segment_norm e hew hκ hρ]
    have : |2 * s - 1 / 2 - 1 / 2| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    gcongr
  have hd := rescaleMap_dist_le e y w hκ hρ hρ1 p (y - (1 / 2 : ℝ) • w + s • (2 • w))
  have hdist : κ * ρ⁻¹ * dist p (y - (1 / 2 : ℝ) • w + s • (2 • w)) < 2 * κ := by
    calc
      κ * ρ⁻¹ * dist p (y - (1 / 2 : ℝ) • w + s • (2 • w)) < κ * ρ⁻¹ * (2 * ρ) := by gcongr
      _ = 2 * κ := by field_simp
  have hn := norm_le_norm_add_norm_sub
    (rescaleMap e y w hκ hρ (y - (1 / 2 : ℝ) • w + s • (2 • w))) (rescaleMap e y w hκ hρ p)
  rw [norm_sub_rev, ← dist_eq_norm] at hn
  linarith

/-- The stretched direction of a tube in the `ρ`-tube has length at most `5`. -/
theorem stretch_dir_norm_le (e : Space ≃ₗᵢ[ℝ] Space) {w : Space} (hew : e w = axis)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {v : Space} (hvw : pd v w < 4 * ρ) :
    ‖stretch ρ⁻¹ (e v)‖ ≤ 5 := by
  have hcap : pd (e v) axis ≤ 4 * ρ := by
    rw [← hew, pd_isometry]; exact hvw.le
  have h := norm_stretch_cap ((one_le_inv₀ hρ).mpr hρ1) hcap
  calc
    ‖stretch ρ⁻¹ (e v)‖ ≤ 1 + ρ⁻¹ * (4 * ρ) := h
    _ = 5 := by field_simp; ring

theorem stretch_dir_ne_zero (e : Space ≃ₗᵢ[ℝ] Space) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {v : Space} (hv : ‖v‖ = 1) : stretch ρ⁻¹ (e v) ≠ 0 := by
  have h := norm_le_stretch ((one_le_inv₀ hρ).mpr hρ1) (e v)
  rw [e.norm_map, hv] at h
  exact norm_ne_zero_iff.mp (by linarith)

/-- The direction of the rescaled tube. -/
def rescaledDir (e : Space ≃ₗᵢ[ℝ] Space) (ρ : ℝ) (v : Space) : Space :=
  unit (stretch ρ⁻¹ (e v))

/-- The base point of the rescaled tube: the image of the midpoint, moved back half a unit. -/
def rescaledBase (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    (x v : Space) : Space :=
  rescaleMap e y w hκ hρ (x + (1 / 2 : ℝ) • v) - (1 / 2 : ℝ) • rescaledDir e ρ v

theorem norm_rescaledDir (e : Space ≃ₗᵢ[ℝ] Space) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {v : Space} (hv : ‖v‖ = 1) : ‖rescaledDir e ρ v‖ = 1 :=
  norm_unit (stretch_dir_ne_zero e hρ hρ1 hv)

/-- The image of a `δ`-tube of the fibre lies in the exact rescaled tube. -/
theorem rescale_image_tube_subset (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space} (hew : e w = axis)
    {κ ρ δ : ℝ} (hκ : 0 < κ) (hκ5 : κ * 5 ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {x v : Space} (hv : ‖v‖ = 1) (hvw : pd v w < 4 * ρ) :
    rescaleMap e y w hκ hρ '' Tube δ x v ⊆
      Tube (κ * ρ⁻¹ * δ) (rescaledBase e y w hκ hρ x v) (rescaledDir e ρ v) := by
  have hne := stretch_dir_ne_zero e hρ hρ1 hv
  have hL := stretch_dir_norm_le e hew hρ hρ1 hvw
  have h := image_tube_extend (rescaleMap e y w hκ hρ) x v (rescaledDir e ρ v)
    (δ := δ) (l := κ * ‖stretch ρ⁻¹ (e v)‖) (A := κ * ρ⁻¹) (by positivity) (by positivity)
    ((mul_le_mul_of_nonneg_left hL hκ.le).trans hκ5)
    (by
      change κ • stretch ρ⁻¹ (e v) = (κ * ‖stretch ρ⁻¹ (e v)‖) • unit (stretch ρ⁻¹ (e v))
      rw [mul_smul, norm_smul_unit hne])
    (rescaleMap_dist_le e y w hκ hρ hρ1)
  exact h

/-- The rescaled tube lies in the unit ball as soon as its radius is at most `1/100`. -/
theorem rescaled_tube_subset_ball (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space} (hew : e w = axis)
    {κ ρ δ : ℝ} (hκ : 0 < κ) (hκ6 : κ * 6 ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ)
    (hδ' : κ * ρ⁻¹ * δ ≤ 1 / 100) {x v : Space} (hv : ‖v‖ = 1)
    (hsub : Tube δ x v ⊆ Tube ρ y w) :
    Tube (κ * ρ⁻¹ * δ) (rescaledBase e y w hκ hρ x v) (rescaledDir e ρ v) ⊆
      Metric.ball (0 : Space) 1 := by
  have hmid : x + (1 / 2 : ℝ) • v ∈ Tube ρ y w := by
    apply hsub
    apply self_subset_thickening hδ
    rw [segment_eq_image']
    exact ⟨1 / 2, by norm_num, by simp⟩
  have hn := rescaleMap_tube_norm_lt e hew hκ hρ hρ1 hmid
  exact centered_tube_subset_ball (norm_rescaledDir e hρ hρ1 hv) (by linarith) hδ'

end

end WangZahlLot.Obl.wz_rescaled_tube_estimate
