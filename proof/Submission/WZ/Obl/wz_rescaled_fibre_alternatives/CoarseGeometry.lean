-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.CoarseGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.PullbackGeometry

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

noncomputable section

lemma tube_midpoints_close {s ρ : ℝ} (hs : 0 < s) {x v z u : Space}
    (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) (h : tube s x v ⊆ tube ρ z u) :
    dist (x + (1 / 2 : ℝ) • v) (z + (1 / 2 : ℝ) • u) < 3 * ρ := by
  have h₀ := h (self_subset_thickening hs _ (left_mem_segment _ _ _))
  have h₁ := h (self_subset_thickening hs _ (right_mem_segment _ _ _))
  rcases WangZahlLot.Obl.wz_tower_convex_count_composition.parent_endpoints hv hu h₀ h₁ with hh | hh
  · have he : x + (1 / 2 : ℝ) • v - (z + (1 / 2 : ℝ) • u) =
        (1 / 2 : ℝ) • ((x - z) + (x + v - (z + u))) := by module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
    norm_num
    simp only [dist_eq_norm] at hh
    have hn := norm_add_le (x - z) (x + v - (z + u))
    rw [norm_sub_rev x z, norm_sub_rev (x + v) (z + u)] at hn
    linarith [hh.1, hh.2]
  · have he : x + (1 / 2 : ℝ) • v - (z + (1 / 2 : ℝ) • u) =
        (1 / 2 : ℝ) • ((x - (z + u)) + (x + v - z)) := by module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
    norm_num
    simp only [dist_eq_norm] at hh
    have hn := norm_add_le (x - (z + u)) (x + v - z)
    rw [norm_sub_rev x (z + u), norm_sub_rev (x + v) z] at hn
    linarith [hh.1, hh.2]

lemma tube_enlarge_inside_parent {r s R : ℝ} (hs : 0 < s) (hR : R ≤ r)
    {x v y w : Space} (h : tube s x v ⊆ tube r y w) :
    tube R x v ⊆ tube (2 * r) y w := by
  have hseg := (self_subset_thickening hs _).trans h
  exact (thickening_subset_of_subset R hseg).trans
    ((thickening_thickening_subset R r _).trans (thickening_mono (by linarith) _))

lemma normalized_coarse_expansion (e : Space ≃ₗᵢ[ℝ] Space) {y w x v z u : Space}
    (hew : e w = axis) {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hρ : 0 < ρ) (hρk : ρ ≤ contraction ^ 2)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : tube s x v ⊆ tube r y w)
    (hf : normalize e y w r hr '' tube s x v ⊆ tube ρ z u) :
    doubled ρ z u ⊆
      AffineMap.homothety (normalize e y w r hr (x + (1 / 2 : ℝ) • v)) dilation ''
        (normalize e y w r hr '' tube (coverScale * r * ρ) x v) := by
  let f := normalize e y w r hr
  apply homothety_image_of_contraction _ (by norm_num [dilation, contraction] : dilation ≠ 0)
  rintro q' ⟨q, hq, rfl⟩
  let p := f.symm q
  have hfp : f p = q := f.apply_symm_apply q
  obtain ⟨A, hA, hnear⟩ := normalize_doubled_near_child e hew hr hr1 hs hρ hρk hv hw hu hT hf
    (q := p) (by rwa [show normalize e y w r hr p = q from hfp])
  have hh : AffineMap.homothety (x + (1 / 2 : ℝ) • v) dilation⁻¹ p ∈
      tube (coverScale * r * ρ) x v := by
    apply homothety_mem_tube (B := 77 * r * ρ / contraction ^ 2) ?_ hnear ?_
    · rw [abs_mul]
      have h := mul_le_mul_of_nonneg_left hA (abs_nonneg dilation⁻¹)
      norm_num [dilation, contraction] at h ⊢
      linarith
    · norm_num [dilation, coverScale, contraction]
      nlinarith [mul_pos hr hρ]
  refine ⟨AffineMap.homothety (x + (1 / 2 : ℝ) • v) dilation⁻¹ p, hh, ?_⟩
  rw [affine_homothety, hfp]

/-- A kept child lies in the doubled physical cover built on a representative. -/
lemma child_in_physical_cover (e : Space ≃ₗᵢ[ℝ] Space) {y w x v x' v' z u : Space}
    (hew : e w = axis) {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1 / 100) (hρ : 0 < ρ)
    (hρsmall : ρ ≤ 1 / (100 * coverScale))
    (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : tube s x v ⊆ tube r y w)
    (hf : normalize e y w r hr '' tube s x v ⊆ tube ρ z u)
    (hf' : normalize e y w r hr '' tube s x' v' ⊆ tube ρ z u)
    (hmid : dist (normalize e y w r hr (x' + (1 / 2 : ℝ) • v'))
      (normalize e y w r hr (x + (1 / 2 : ℝ) • v)) ≤ 6 * ρ) :
    tube s x' v' ⊆ doubled (coverScale * r * ρ) x v := by
  have hscale := coverScale_pos
  have hρk : ρ ≤ contraction ^ 2 := by
    have := hρsmall
    norm_num [coverScale, contraction] at this ⊢
    linarith
  have hR1 : coverScale * r * ρ ≤ 1 / 100 := by
    have hR := (le_div_iff₀ (by positivity : 0 < 100 * coverScale)).mp hρsmall
    have hh := mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ coverScale * ρ)
    nlinarith only [hR, hh]
  have hmid' : ‖(x' + (1 / 2 : ℝ) • v') - (x + (1 / 2 : ℝ) • v)‖ ≤ 6 * ρ / contraction := by
    exact (normalize_inverse_norm e y w hr hr1 _ _).trans
      ((div_le_div_iff_of_pos_right (by norm_num : 0 < contraction)).mpr
        (by simpa only [dist_eq_norm] using hmid))
  intro q hq
  obtain ⟨A, hA, hnear⟩ := normalize_doubled_near_child e hew hr hr1 hs hρ hρk hv hw hu hT hf
    (tube_subset_doubled hρ.le z u (hf' ⟨q, hq, rfl⟩))
  have hdist : ‖q - (x + (1 / 2 : ℝ) • v)‖ < s + 1 / 2 + 6 * ρ / contraction := by
    have hh := tube_dist_midpoint hv' hq
    simp only [dist_eq_norm] at hh
    have hn := norm_sub_le_norm_sub_add_norm_sub q (x' + (1 / 2 : ℝ) • v') (x + (1 / 2 : ℝ) • v)
    linarith
  have herror : 77 * r * ρ / contraction ^ 2 < 1 / 100 := by
    have hh : 77 * r * ρ / contraction ^ 2 = (77 / 1000000 : ℝ) * (coverScale * r * ρ) := by
      unfold coverScale
      ring
    rw [hh]
    linarith
  have hnorm : |A| ≤ 1 := by
    have hn := norm_le_norm_add_norm_sub (q - (x + (1 / 2 : ℝ) • v)) (A • v)
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one] at hn
    have hρ' : 6 * ρ / contraction ≤ 1 / 100 := by
      have hh := hρsmall
      norm_num [coverScale, contraction] at hh ⊢
      linarith
    linarith
  apply mem_thickening_iff.mpr
  refine ⟨x + (1 / 2 : ℝ) • v + A • v, centered_doubled_segment x v hnorm, ?_⟩
  rw [dist_eq_norm, ← sub_sub]
  apply hnear.trans_lt
  norm_num [coverScale, contraction]
  nlinarith [mul_pos hr hρ]

end
end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
