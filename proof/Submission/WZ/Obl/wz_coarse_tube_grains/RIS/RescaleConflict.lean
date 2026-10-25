-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.RescaleConflict.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleGeometry

/-!
# Conflicting rescaled tubes come from tubes near a common axis

If two rescaled tubes of a fibre overlap in more than half of their volume, then the original
`δ`-tubes have directions within `5000000 κ δ` (up to sign), and their midpoints differ by a
multiple of the first direction up to `500015 δ`. The transverse stretch by `ρ⁻¹` is what makes
these bounds independent of `ρ`.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_affine_robust_cluster_estimate

noncomputable section

/-- The rescaled tube of a fibre tube. -/
abbrev rescaledTube (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space) {κ ρ : ℝ} (hκ : 0 < κ)
    (hρ : 0 < ρ) (δ : ℝ) (x v : Space) : Set Space :=
  Tube (κ * ρ⁻¹ * δ) (rescaledBase e y w hκ hρ x v) (rescaledDir e ρ v)

/-- Midpoints of fibre tubes are at distance less than `3` from each other. -/
theorem midpoint_dist_lt {δ ρ : ℝ} (hδ : 0 < δ) (hρ1 : ρ ≤ 1) {x v x' v' y w : Space}
    (hw : ‖w‖ = 1) (hsub : Tube δ x v ⊆ Tube ρ y w) (hsub' : Tube δ x' v' ⊆ Tube ρ y w) :
    ‖(x' + (1 / 2 : ℝ) • v') - (x + (1 / 2 : ℝ) • v)‖ < 3 := by
  have hmid : ∀ {a b : Space}, Tube δ a b ⊆ Tube ρ y w →
      ∃ s ∈ Icc (0 : ℝ) 1, ‖(a + (1 / 2 : ℝ) • b) - (y + s • w)‖ < ρ := by
    intro a b hab
    have hm : a + (1 / 2 : ℝ) • b ∈ Tube ρ y w := by
      apply hab
      apply self_subset_thickening hδ
      rw [segment_eq_image']
      exact ⟨1 / 2, by norm_num, by simp⟩
    obtain ⟨q, hq, hmq⟩ := mem_thickening_iff.mp hm
    rw [segment_eq_image'] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    simp only [add_sub_cancel_left] at hmq
    exact ⟨s, hs, by rwa [dist_eq_norm] at hmq⟩
  obtain ⟨s, hs, h1⟩ := hmid hsub
  obtain ⟨s', hs', h2⟩ := hmid hsub'
  have heq : (x' + (1 / 2 : ℝ) • v') - (x + (1 / 2 : ℝ) • v) =
      ((x' + (1 / 2 : ℝ) • v') - (y + s' • w)) - ((x + (1 / 2 : ℝ) • v) - (y + s • w)) +
        (s' - s) • w := by module
  rw [heq]
  have h3 : ‖(s' - s) • w‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one]
    exact abs_le.mpr ⟨by linarith [hs.2, hs'.1], by linarith [hs.1, hs'.2]⟩
  have h4 := norm_add_le (((x' + (1 / 2 : ℝ) • v') - (y + s' • w)) -
    ((x + (1 / 2 : ℝ) • v) - (y + s • w))) ((s' - s) • w)
  have h5 := norm_sub_le ((x' + (1 / 2 : ℝ) • v') - (y + s' • w))
    ((x + (1 / 2 : ℝ) • v) - (y + s • w))
  linarith

/-- Conflict control needs only angular confinement and a midpoint-distance bound. -/
theorem near_axis_of_rescaled_conflict_of_bounds (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {κ ρ δ L : ℝ} (hκ : 0 < κ) (hκ5 : κ * 5 ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ) {x v x' v' : Space} (hv : ‖v‖ = 1)
    (hv' : ‖v'‖ = 1) (hvw : pd v w < 4 * ρ) (hvw' : pd v' w < 4 * ρ)
    (hmid : ‖(x' + (1 / 2 : ℝ) • v') - (x + (1 / 2 : ℝ) • v)‖ ≤ L)
    (hbad : ¬ volume (rescaledTube e y w hκ hρ δ x v ∩ rescaledTube e y w hκ hρ δ x' v') ≤
      (1 / 2 : ENNReal) * volume (rescaledTube e y w hκ hρ δ x v)) :
    pd v v' ≤ 5000000 * κ * δ ∧
      ∃ s : ℝ, |s| ≤ L ∧
        ‖(x' + (1 / 2 : ℝ) • v') - (x + (1 / 2 : ℝ) • v) - s • v‖ ≤ 500015 * δ := by
  set t : ℝ := ρ⁻¹ with ht_def
  have ht : 1 ≤ t := (one_le_inv₀ hρ).mpr hρ1
  have htpos : 0 < t := by linarith
  set δ' : ℝ := κ * t * δ with hδ'_def
  have hδ' : 0 < δ' := by positivity
  set u := rescaledDir e ρ v with hu_def
  set u' := rescaledDir e ρ v' with hu'_def
  have hu : ‖u‖ = 1 := norm_rescaledDir e hρ hρ1 hv
  have hu' : ‖u'‖ = 1 := norm_rescaledDir e hρ hρ1 hv'
  have hL : ‖stretch t (e v)‖ ≤ 5 := stretch_dir_norm_le e hew hρ hρ1 hvw
  have hL' : ‖stretch t (e v')‖ ≤ 5 := stretch_dir_norm_le e hew hρ hρ1 hvw'
  constructor
  · -- directions
    have hpd' : pd u u' ≤ 100000 * δ' := by
      by_contra hfar
      push Not at hfar
      apply hbad
      apply wz_direction_density_transfer.intersection_le_half hδ' hu hu'
      · exact hfar.le.trans (min_le_left _ _)
      · exact hfar.le.trans (min_le_right _ _)
    have hs := pd_stretch ht (by norm_num : (0 : ℝ) ≤ 5)
      (by rw [e.norm_map]; exact hv : ‖e v‖ = 1) (by rw [e.norm_map]; exact hv' : ‖e v'‖ = 1)
      hL hL'
    rw [pd_isometry] at hs
    change t * pd v v' ≤ 2 * 5 ^ 2 * pd u u' at hs
    have h1 : t * pd v v' ≤ t * (5000000 * κ * δ) := by
      calc
        t * pd v v' ≤ 2 * 5 ^ 2 * pd u u' := hs
        _ ≤ 2 * 5 ^ 2 * (100000 * δ') := by gcongr
        _ = t * (5000000 * κ * δ) := by rw [hδ'_def]; ring
    exact le_of_mul_le_mul_left h1 htpos
  · -- positions
    set F := rescaleMap e y w hκ hρ with hF_def
    set m := x + (1 / 2 : ℝ) • v with hm_def
    set m' := x' + (1 / 2 : ℝ) • v' with hm'_def
    have hcyl := conflicting_tube_subset_cylinder hδ' hu hu' hbad
    have hFm' : F m' ∈ rescaledTube e y w hκ hρ δ x' v' := by
      apply self_subset_thickening hδ'
      rw [segment_eq_image']
      refine ⟨1 / 2, by norm_num, ?_⟩
      simp only [rescaledBase, ← hu'_def, ← hF_def, ← hm'_def]
      module
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp (hcyl hFm')
    rw [segment_eq_image'] at hq
    obtain ⟨τ, -, rfl⟩ := hq
    simp only [add_sub_cancel_left] at hpq
    rw [dist_eq_norm] at hpq
    -- `F m' - F m = κ • stretch t (e (m' - m))`
    have hsubF : F m' - F m = κ • stretch t (e (m' - m)) := rescaleMap_sub e y w hκ hρ m' m
    set σ₀ : ℝ := 6 * τ - 5 / 2 with hσ₀
    have hclose : ‖κ • stretch t (e (m' - m)) - σ₀ • u‖ < 100003 * δ' := by
      have heq : κ • stretch t (e (m' - m)) - σ₀ • u =
          F m' - (rescaledBase e y w hκ hρ x v - (2 : ℝ) • u + τ • ((6 : ℝ) • u)) := by
        rw [← hsubF]
        simp only [rescaledBase, ← hu_def, ← hF_def, ← hm_def, hσ₀]
        module
      rw [heq]
      exact hpq
    have herr : ‖stretch t (e (m' - m)) - (σ₀ / κ) • unit (stretch t (e v))‖ ≤
        100003 * t * δ := by
      have heq : stretch t (e (m' - m)) - (σ₀ / κ) • unit (stretch t (e v)) =
          κ⁻¹ • (κ • stretch t (e (m' - m)) - σ₀ • u) := by
        rw [hu_def]
        unfold rescaledDir
        rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hκ.ne', one_smul, ← ht_def]
        congr 1
        rw [div_eq_inv_mul]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hκ]
      calc
        κ⁻¹ * ‖κ • stretch t (e (m' - m)) - σ₀ • u‖ ≤ κ⁻¹ * (100003 * δ') := by
          gcongr
        _ = 100003 * t * δ := by rw [hδ'_def]; field_simp
    have hperp := perpendicular_distance_of_stretched_line_error ht (by positivity)
      (by rw [e.norm_map]; exact hv : ‖e v‖ = 1) hL herr
    have hperp' : ‖(m' - m) - (inner ℝ v (m' - m)) • v‖ ≤ 500015 * δ := by
      have hiso : e (m' - m) - (inner ℝ (e v) (e (m' - m))) • e v =
          e ((m' - m) - (inner ℝ v (m' - m)) • v) := by
        rw [LinearIsometryEquiv.inner_map_map]
        simp only [map_sub, map_smul]
      rw [hiso, e.norm_map] at hperp
      calc
        _ ≤ 5 * (100003 * t * δ) / t := hperp
        _ = 500015 * δ := by field_simp; ring
    refine ⟨inner ℝ v (m' - m), ?_, hperp'⟩
    have hin := abs_real_inner_le_norm v (m' - m)
    rw [hv, one_mul] at hin
    exact hin.trans hmid

/-- Conflicting rescaled tubes in a unit carrier force near-axis original parameters. -/
theorem near_axis_of_rescaled_conflict (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) (hw : ‖w‖ = 1) {κ ρ δ : ℝ} (hκ : 0 < κ) (hκ5 : κ * 5 ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ) {x v x' v' : Space} (hv : ‖v‖ = 1)
    (hv' : ‖v'‖ = 1) (hsub : Tube δ x v ⊆ Tube ρ y w) (hsub' : Tube δ x' v' ⊆ Tube ρ y w)
    (hbad : ¬ volume (rescaledTube e y w hκ hρ δ x v ∩ rescaledTube e y w hκ hρ δ x' v') ≤
      (1 / 2 : ENNReal) * volume (rescaledTube e y w hκ hρ δ x v)) :
    pd v v' ≤ 5000000 * κ * δ ∧
      ∃ s : ℝ, |s| ≤ 3 ∧
        ‖(x' + (1 / 2 : ℝ) • v') - (x + (1 / 2 : ℝ) • v) - s • v‖ ≤ 500015 * δ :=
  near_axis_of_rescaled_conflict_of_bounds e hew hκ hκ5 hρ hρ1 hδ hv hv'
    (pd_lt_of_tube_subset hδ hv hw hsub) (pd_lt_of_tube_subset hδ hv' hw hsub')
    (midpoint_dist_lt hδ hρ1 hw hsub hsub').le hbad

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
