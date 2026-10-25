-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.ShadingExpansion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RescaleGeometry

/-! # Transverse expansion of a tube shading -/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open wz_affine_robust_cluster_estimate

noncomputable section

/-- Expand about the axis through `x`, retaining the original ambient coordinates. -/
def tubeExpand (e : Space ≃ₗᵢ[ℝ] Space) (x : Space) (t : ℝ) (p : Space) : Space :=
  x + e.symm (stretch t (e (p - x)))

theorem tubeExpand_volume (e : Space ≃ₗᵢ[ℝ] Space) (x : Space) (t : ℝ)
    (Y : Set Space) :
    volume (tubeExpand e x t '' Y) = ENNReal.ofReal (t ^ 2) * volume Y := by
  have he : tubeExpand e x t '' Y =
      (fun q : Space => x + q) '' (e.symm '' (stretch t '' (e ''
        ((fun p : Space => p - x) '' Y)))) := by
    simp only [image_image]
    rfl
  rw [he]
  simp only [image_add_left, measure_preimage_add]
  rw [volume_rotation, Measure.addHaar_image_linearMap, det_stretch,
    abs_of_nonneg (sq_nonneg t), volume_rotation]
  simp only [sub_eq_add_neg, image_add_right, measure_preimage_add_right]

private theorem norm_stretch_sub_le {t : ℝ} (ht : 1 ≤ t) (u : Space) :
    ‖stretch t u - u‖ ≤ (t - 1) * ‖u‖ := by
  have ht0 : 0 ≤ t - 1 := by linarith
  have hsq : ‖stretch t u - u‖ ^ 2 ≤ ((t - 1) * ‖u‖) ^ 2 := by
    rw [norm_sq_coords, mul_pow, norm_sq_coords]
    simp only [PiLp.sub_apply, stretch_zero, stretch_one, stretch_two]
    nlinarith [mul_nonneg (sq_nonneg (t - 1)) (sq_nonneg (u 0))]
  nlinarith [norm_nonneg (stretch t u - u), norm_nonneg u,
    mul_nonneg ht0 (norm_nonneg u)]

theorem tubeExpand_mem {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (e : Space ≃ₗᵢ[ℝ] Space) {x v : Space} (hev : e v = axis)
    {p : Space} (hp : p ∈ Tube δ x v) :
    tubeExpand e x (ρ / δ) p ∈ Tube ρ x v ∧
      dist (tubeExpand e x (ρ / δ) p) p < ρ := by
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have ht : 1 ≤ ρ / δ := (one_le_div hδ).mpr hδρ
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  let u := e (p - (x + s • v))
  have hu : ‖u‖ < δ := by
    change ‖e (p - (x + s • v))‖ < δ
    rw [e.norm_map]
    exact hpq
  have heq : e (p - x) = u + s • axis := by
    dsimp only [u]
    rw [← hev, ← map_smul, ← map_add]
    congr 1
    module
  have haxis : e.symm axis = v := by rw [← hev, e.symm_apply_apply]
  have hexpand : tubeExpand e x (ρ / δ) p = x + s • v + e.symm (stretch (ρ / δ) u) := by
    rw [tubeExpand, heq, map_add, map_smul, stretch_axis, map_add, map_smul, haxis]
    abel
  have hpdec : p = x + s • v + e.symm u := by
    simp only [u, e.symm_apply_apply]
    abel
  constructor
  · apply mem_thickening_iff.mpr
    refine ⟨x + s • v, ?_, ?_⟩
    · rw [segment_eq_image']
      exact ⟨s, hs, by simp⟩
    · rw [hexpand, dist_eq_norm, add_sub_cancel_left, e.symm.norm_map]
      calc
        ‖stretch (ρ / δ) u‖ ≤ (ρ / δ) * ‖u‖ := norm_stretch_le ht u
        _ < (ρ / δ) * δ := mul_lt_mul_of_pos_left hu (div_pos hρ hδ)
        _ = ρ := div_mul_cancel₀ _ hδ.ne'
  · rw [hexpand, dist_eq_norm, show x + s • v + e.symm (stretch (ρ / δ) u) - p =
        e.symm (stretch (ρ / δ) u - u) by rw [map_sub, hpdec]; abel]
    rw [e.symm.norm_map]
    calc
      ‖stretch (ρ / δ) u - u‖ ≤ (ρ / δ - 1) * ‖u‖ := norm_stretch_sub_le ht u
      _ ≤ (ρ / δ - 1) * δ := mul_le_mul_of_nonneg_left hu.le (by linarith)
      _ = ρ - δ := by field_simp
      _ < ρ := by linarith

/-- A thickened shading inside its enlarged tube gains the full transverse area factor. -/
theorem volume_thickening_tube_shading {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    {x v : Space} (hv : ‖v‖ = 1) {Y : Set Space} (hY : Y ⊆ Tube δ x v) :
    ENNReal.ofReal ((ρ / δ) ^ 2) * volume Y ≤
      volume (Tube ρ x v ∩ thickening ρ Y) := by
  obtain ⟨e, hev⟩ := exists_rotation hv
  rw [← tubeExpand_volume e x (ρ / δ) Y]
  apply measure_mono
  rintro _ ⟨p, hp, rfl⟩
  have hm := tubeExpand_mem hδ hδρ e hev (hY hp)
  exact ⟨hm.1, mem_thickening_iff.mpr ⟨p, hp, hm.2⟩⟩

/-- Thickening a dense tube shading preserves its density at every larger radius. -/
theorem thickening_tube_shading_dense {δ ρ ℓ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    {x v : Space} (hv : ‖v‖ = 1) {Y : Set Space} (hY : Y ⊆ Tube δ x v)
    (hdense : ENNReal.ofReal (ℓ * δ ^ 2) ≤ volume Y) :
    ENNReal.ofReal (ℓ * ρ ^ 2) ≤ volume (Tube ρ x v ∩ thickening ρ Y) := by
  calc
    ENNReal.ofReal (ℓ * ρ ^ 2) =
        ENNReal.ofReal ((ρ / δ) ^ 2) * ENNReal.ofReal (ℓ * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal ((ρ / δ) ^ 2) * volume Y := mul_le_mul_right hdense _
    _ ≤ _ := volume_thickening_tube_shading hδ hδρ hv hY

/-- Average fine-tube density supplies one shading with the same normalized density. -/
theorem exists_dense_fine_shading {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    {δ ℓ : ℝ} (hℓ : 0 ≤ ℓ) {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hY : ∀ i ∈ S, Y i ⊆ Tube δ (x i) (v i))
    (hdense : ENNReal.ofReal (ℓ * S.card * δ ^ 2) ≤ ∑ i ∈ S, volume (Y i)) :
    ∃ i ∈ S, ENNReal.ofReal (ℓ * δ ^ 2) ≤ volume (Y i) := by
  have hfin (i) (hi : i ∈ S) : volume (Y i) ≠ ⊤ :=
    ne_top_of_le_ne_top (tube_volume_ne_top _ _ _) (measure_mono (hY i hi))
  have hr := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hfin) hdense
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_sum hfin] at hr
  have hsum : ∑ _i ∈ S, ℓ * δ ^ 2 ≤ ∑ i ∈ S, (volume (Y i)).toReal := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hr
  obtain ⟨i, hi, hdi⟩ := Finset.exists_le_of_sum_le hS hsum
  exact ⟨i, hi, (ENNReal.ofReal_le_ofReal hdi).trans_eq (ENNReal.ofReal_toReal (hfin i hi))⟩

/-- A neighborhood of the union of an average-dense fine family has coarse density.
No disjointness or multiplicity assumption is needed for this step. -/
theorem thickening_family_shading_dense {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    {δ ρ ℓ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hℓ : 0 ≤ ℓ)
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hY : ∀ i ∈ S, Y i ⊆ Tube δ (x i) (v i))
    (hdense : ENNReal.ofReal (ℓ * S.card * δ ^ 2) ≤ ∑ i ∈ S, volume (Y i)) :
    ENNReal.ofReal (ℓ * ρ ^ 2) ≤ volume (thickening ρ (⋃ i ∈ S, Y i)) := by
  obtain ⟨i, hi, hdi⟩ := exists_dense_fine_shading S hS hℓ hY hdense
  refine (thickening_tube_shading_dense hδ hδρ (hv i hi) (hY i hi) hdi).trans
    (measure_mono ?_)
  exact inter_subset_right.trans (thickening_subset_of_subset _
    (subset_biUnion_of_mem hi))

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
