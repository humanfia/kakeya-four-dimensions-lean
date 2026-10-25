-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaleEllipsoid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleDualGeometry

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open LeanEval.Analysis.WangZahlKakeya
open wz_affine_robust_cluster_estimate

/-- An open normalized ball pulls back into the corresponding physical
ball; transverse contraction can only shorten distances. -/
theorem rescale_preimage_ball_subset_ball (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space)
    {κ ρ r : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p₀ : Space) :
    (rescaleMap e y w hκ hρ) ⁻¹' Metric.ball (rescaleMap e y w hκ hρ p₀) (κ * r) ⊆
      Metric.ball p₀ r := by
  intro p hp
  have hh : ‖rescaleMap e y w hκ hρ p - rescaleMap e y w hκ hρ p₀‖ < κ * r := by
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hp
  rw [rescaleMap_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hκ] at hh
  have hs : ‖stretch ρ⁻¹ (e (p - p₀))‖ < r := (mul_lt_mul_iff_right₀ hκ).mp hh
  have hn := (norm_le_stretch ((one_le_inv₀ hρ).mpr hρ1) (e (p - p₀))).trans_lt hs
  simpa only [Metric.mem_ball, dist_eq_norm, e.norm_map] using hn

/-- A radius-kappa*r ball pulls back to an ellipsoid of axial radius r and
transverse radius rho*r. -/
theorem rescale_ball_axial_transverse (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {κ ρ r : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hr : 0 ≤ r) (p p₀ : Space)
    (hball : ‖rescaleMap e y w hκ hρ p - rescaleMap e y w hκ hρ p₀‖ ≤ κ * r) :
    ‖p - p₀‖ ≤ r ∧ |inner ℝ w (p - p₀)| ≤ r ∧
      ‖(p - p₀) - (inner ℝ w (p - p₀)) • w‖ ≤ ρ * r := by
  rw [rescaleMap_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hκ] at hball
  have hscaled : ‖stretch ρ⁻¹ (e (p - p₀))‖ ≤ r :=
    (mul_le_mul_iff_right₀ hκ).mp hball
  have hnorm : ‖p - p₀‖ ≤ r := by
    have hh := (norm_le_stretch ((one_le_inv₀ hρ).mpr hρ1) (e (p - p₀))).trans hscaled
    simpa only [e.norm_map] using hh
  have hw : ‖w‖ = 1 := by rw [← e.norm_map w, hew, norm_axis]
  refine ⟨hnorm, (abs_real_inner_le_norm w (p - p₀)).trans (by simpa [hw] using hnorm), ?_⟩
  have hperp := perpendicular_distance_of_stretched_line_error
    ((one_le_inv₀ hρ).mpr hρ1) hr norm_axis
    (by simp only [stretch_axis, norm_axis]; norm_num : ‖stretch ρ⁻¹ axis‖ ≤ (1 : ℝ))
    (s := 0) (q := e (p - p₀)) (by simpa using hscaled)
  have hi : inner ℝ axis (e (p - p₀)) = inner ℝ w (p - p₀) := by
    rw [← hew, e.inner_map_map]
  have he : e ((p - p₀) - (inner ℝ w (p - p₀)) • w) =
      e (p - p₀) - (inner ℝ axis (e (p - p₀))) • axis := by
    rw [map_sub, map_smul, hew, hi]
  rw [← he, e.norm_map] at hperp
  convert hperp using 1 <;> field_simp

/-- Slabs supplied by the normalized planar lemma pull back to halfwidth
at most twenty fine radii. -/
theorem rescaled_fine_slab_pullback (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {κ ρ δ τ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 ≤ δ) {v u : Space} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1)
    (hvw : pd v w < 4 * ρ) (hτ : τ ≤ 1 / 10)
    (hnormal : |inner ℝ u (rescaledDir e ρ v)| ≤ τ)
    (p p₀ : Space) (t : ℝ)
    (hslab : |inner ℝ u (rescaleMap e y w hκ hρ p) - t| ≤ 2 * (κ * ρ⁻¹ * δ)) :
    |inner ℝ (unit (pullbackNormal e ρ u)) (p - p₀) -
      (t - inner ℝ u (rescaleMap e y w hκ hρ p₀)) /
        (κ * ‖pullbackNormal e ρ u‖)| ≤ 20 * δ := by
  have hh := rescaled_slab_pullback e y w hκ hρ hρ1 hu p p₀ t _ hslab
  have hN : 0 < ‖pullbackNormal e ρ u‖ := norm_pos_iff.mpr (pullbackNormal_ne_zero e hρ hρ1 hu)
  have hlow := dual_stretch_norm_lower e hew hρ hρ1 hv hu hvw hτ hnormal
  rw [← norm_pullbackNormal e] at hlow
  apply hh.trans
  apply (div_le_iff₀ (mul_pos hκ hN)).mpr
  calc
    2 * (κ * ρ⁻¹ * δ) = (20 * κ * δ) * (1 / (10 * ρ)) := by field_simp; ring
    _ ≤ (20 * κ * δ) * ‖pullbackNormal e ρ u‖ :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    _ = _ := by ring

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
