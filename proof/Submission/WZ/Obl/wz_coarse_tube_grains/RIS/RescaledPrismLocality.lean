-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaledPrismLocality.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleEllipsoid
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismLocality

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_affine_robust_cluster_estimate

/-- The transverse displacement of points in an adapted grain has the
coarse-radius factor, even along its long axis. -/
theorem prism_perpendicular_bound {a b c ρ : ℝ} {z p w : V}
    (hρ : 0 < ρ) (hρ100 : ρ ≤ 1 / 100) (hc : 0 ≤ c)
    (hab : a ≤ b) (hbr : b ≤ 128 * ρ * c) (hw : ‖w‖ = 1)
    (e : V ≃ₗᵢ[ℝ] V) (halign : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2)
    (hp : p ∈ P a b c z e) :
    ‖(p - z) - (inner ℝ w (p - z)) • w‖ ≤ 256 * ρ * c := by
  let q := p - z
  have hq0 : |e q 0| ≤ 64 * ρ * c := by
    have hh : |e q 0| ≤ a / 2 := hp.1
    linarith
  have hq1 : |e q 1| ≤ 64 * ρ * c := by
    have hh : |e q 1| ≤ b / 2 := hp.2.1
    linarith
  have hq2 : |e q 2| ≤ c / 2 := hp.2.2
  have hw0 : |e w 0| ≤ 10 * ρ := by
    nlinarith [sq_nonneg (e w 1), sq_abs (e w 0), abs_nonneg (e w 0)]
  have hw1 : |e w 1| ≤ 10 * ρ := by
    nlinarith [sq_nonneg (e w 0), sq_abs (e w 1), abs_nonneg (e w 1)]
  have hw2 : |e w 2| ≤ 1 := by simpa only [hw] using abs_rotated_coord_le e w 2
  have h01 : |e q 0 * e w 1 - e q 1 * e w 0| ≤ 128 * ρ * c := by
    calc
      _ ≤ |e q 0 * e w 1| + |e q 1 * e w 0| := abs_sub _ _
      _ ≤ (64 * ρ * c) * (10 * ρ) + (64 * ρ * c) * (10 * ρ) := by
        rw [abs_mul, abs_mul]
        gcongr
      _ = (1280 * ρ) * (ρ * c) := by ring
      _ ≤ 128 * (ρ * c) := by gcongr; linarith
      _ = _ := by ring
  have h02 : |e q 0 * e w 2 - e q 2 * e w 0| ≤ 128 * ρ * c := by
    calc
      _ ≤ |e q 0 * e w 2| + |e q 2 * e w 0| := abs_sub _ _
      _ ≤ (64 * ρ * c) * 1 + (c / 2) * (10 * ρ) := by
        rw [abs_mul, abs_mul]
        gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hρ.le hc]
  have h12 : |e q 1 * e w 2 - e q 2 * e w 1| ≤ 128 * ρ * c := by
    calc
      _ ≤ |e q 1 * e w 2| + |e q 2 * e w 1| := abs_sub _ _
      _ ≤ (64 * ρ * c) * 1 + (c / 2) * (10 * ρ) := by
        rw [abs_mul, abs_mul]
        gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hρ.le hc]
  have hsq (s : ℝ) (hs : |s| ≤ 128 * ρ * c) : s ^ 2 ≤ (128 * ρ * c) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 128 * ρ * c)).mpr hs
  have hperp : ‖q - (inner ℝ w q) • w‖ ^ 2 = areaSq (e q) (e w) := by
    rw [perpendicular_norm_sq hw, areaSq_gram, areaSq_gram,
      e.norm_map, e.norm_map, e.inner_map_map]
  have harea : ‖q - (inner ℝ w q) • w‖ ^ 2 ≤ 3 * (128 * ρ * c) ^ 2 := by
    rw [hperp, areaSq]
    nlinarith only [hsq _ h01, hsq _ h02, hsq _ h12]
  change ‖q - (inner ℝ w q) • w‖ ≤ _
  nlinarith [norm_nonneg (q - (inner ℝ w q) • w), mul_nonneg hρ.le hc]

/-- The anisotropic dilation is bounded by the axial norm plus the
rescaled transverse norm. -/
theorem norm_stretch_rotated_le (E : V ≃ₗᵢ[ℝ] V) {w : V}
    (hew : E w = axis) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (q : V) :
    ‖stretch ρ⁻¹ (E q)‖ ≤ |inner ℝ w q| + ρ⁻¹ * ‖q - (inner ℝ w q) • w‖ := by
  have he : stretch ρ⁻¹ (E q) = (inner ℝ w q) • axis +
      stretch ρ⁻¹ (E (q - (inner ℝ w q) • w)) := by
    rw [map_sub, map_smul, hew, map_sub, map_smul, stretch_axis]
    module
  rw [he]
  calc
    _ ≤ ‖(inner ℝ w q) • axis‖ + ‖stretch ρ⁻¹ (E (q - (inner ℝ w q) • w))‖ := norm_add_le _ _
    _ ≤ |inner ℝ w q| + ρ⁻¹ * ‖q - (inner ℝ w q) • w‖ := by
      rw [norm_smul, Real.norm_eq_abs, norm_axis, mul_one]
      apply add_le_add_right
      simpa only [E.norm_map] using norm_stretch_le ((one_le_inv₀ hρ).mpr hρ1)
        (E (q - (inner ℝ w q) • w))

/-- An adapted prism of length c has diameter O(kappa*c) after rescaling. -/
theorem rescale_prism_norm_sub_center {a b c κ ρ : ℝ} {z p y w : V}
    (hκ : 0 < κ) (hρ : 0 < ρ) (hρ100 : ρ ≤ 1 / 100) (hc : 0 ≤ c)
    (hab : a ≤ b) (hbc : b ≤ c) (hbr : b ≤ 128 * ρ * c) (hw : ‖w‖ = 1)
    (e E : V ≃ₗᵢ[ℝ] V) (hew : E w = axis)
    (halign : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2)
    (hp : p ∈ P a b c z e) :
    ‖rescaleMap E y w hκ hρ p - rescaleMap E y w hκ hρ z‖ ≤ 512 * κ * c := by
  have hnorm := prism_norm_sub_center_le (hab.trans hbc) hbc hc e hp
  have hperp := prism_perpendicular_bound hρ hρ100 hc hab hbr hw e halign hp
  have haxial : |inner ℝ w (p - z)| ≤ c :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [hw, one_mul] using hnorm)
  have hstretch := norm_stretch_rotated_le E hew hρ (by linarith) (p - z)
  have hsize : ‖stretch ρ⁻¹ (E (p - z))‖ ≤ 512 * c := by
    calc
      _ ≤ c + ρ⁻¹ * (256 * ρ * c) := hstretch.trans
        (add_le_add haxial (mul_le_mul_of_nonneg_left hperp (inv_nonneg.mpr hρ.le)))
      _ = 257 * c := by field_simp; ring
      _ ≤ _ := by linarith
  rw [rescaleMap_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
  nlinarith [mul_le_mul_of_nonneg_left hsize hκ.le]

/-- Triple-ball locality survives pulling the local planar cells back from
normalized coordinates, provided the grain length is small enough. -/
theorem rescale_prism_subset_triple_ball {a b c κ ρ r : ℝ} {z p₀ y w : V}
    (hκ : 0 < κ) (hρ : 0 < ρ) (hρ100 : ρ ≤ 1 / 100) (hc : 0 ≤ c)
    (hab : a ≤ b) (hbc : b ≤ c) (hbr : b ≤ 128 * ρ * c) (hcr : 512 * c ≤ r)
    (hw : ‖w‖ = 1) (e E : V ≃ₗᵢ[ℝ] V) (hew : E w = axis)
    (halign : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2)
    (hmeet : (P a b c z e ∩ (rescaleMap E y w hκ hρ) ⁻¹'
      ball (rescaleMap E y w hκ hρ p₀) (κ * r)).Nonempty) :
    rescaleMap E y w hκ hρ '' P a b c z e ⊆
      ball (rescaleMap E y w hκ hρ p₀) (3 * (κ * r)) := by
  let F := rescaleMap E y w hκ hρ
  obtain ⟨q, hqP, hqball⟩ := hmeet
  rintro _ ⟨p, hp, rfl⟩
  have hpz : dist (F p) (F z) ≤ 512 * κ * c := by
    simpa only [dist_eq_norm] using rescale_prism_norm_sub_center hκ hρ hρ100 hc hab hbc hbr hw e E hew halign hp
  have hzq : dist (F z) (F q) ≤ 512 * κ * c := by
    simpa only [dist_eq_norm, norm_sub_rev] using rescale_prism_norm_sub_center hκ hρ hρ100 hc hab hbc hbr hw e E hew halign hqP
  have hqp : dist (F q) (F p₀) < κ * r := mem_ball.mp hqball
  have hh := (dist_triangle (F p) (F z) (F p₀)).trans
    (add_le_add_right (dist_triangle (F z) (F q) (F p₀)) _)
  apply mem_ball.mpr
  nlinarith [mul_le_mul_of_nonneg_left hcr hκ.le]

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
