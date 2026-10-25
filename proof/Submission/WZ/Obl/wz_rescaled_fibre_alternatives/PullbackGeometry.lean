-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.PullbackGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.NearLine

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

noncomputable section

/-- Fixed constants used in all reverse transports. -/
def coverScale : ℝ := 1000000 / contraction ^ 2
def dilation : ℝ := 1000 / contraction
def buffer : ℝ := contraction / 10000

lemma coverScale_pos : 0 < coverScale := by norm_num [coverScale, contraction]
lemma dilation_ge_one : 1 ≤ dilation := by norm_num [dilation, contraction]
lemma buffer_pos : 0 < buffer := by norm_num [buffer, contraction]
lemma buffer_dilation : buffer * (2 * dilation + 2) ≤ 1 := by norm_num [buffer, dilation, contraction]

lemma normalize_doubled_near_child (e : Space ≃ₗᵢ[ℝ] Space) {y w x v z u : Space}
    (hew : e w = axis) {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hρ : 0 < ρ) (hρk : ρ ≤ contraction ^ 2)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : tube s x v ⊆ tube r y w)
    (hf : normalize e y w r hr '' tube s x v ⊆ tube ρ z u)
    {q : Space} (hq : normalize e y w r hr q ∈ doubled ρ z u) :
    ∃ a : ℝ, |a| ≤ 16 / contraction ∧
      ‖q - (x + (1 / 2 : ℝ) • v) - a • v‖ ≤ 77 * r * ρ / contraction ^ 2 := by
  let f := normalize e y w r hr
  have h₀ : f x ∈ tube ρ z u := hf ⟨x, self_subset_thickening hs _ (left_mem_segment _ _ _), rfl⟩
  have h₁ : f (x + v) ∈ tube ρ z u :=
    hf ⟨x + v, self_subset_thickening hs _ (right_mem_segment _ _ _), rfl⟩
  have hlen : contraction ≤ ‖f (x + v) - f x‖ := by
    have hh := normalize_inverse_norm e y w hr hr1 (x + v) x
    rw [add_sub_cancel_left, hv] at hh
    simpa only [one_mul] using (le_div_iff₀ (by norm_num : 0 < contraction)).mp hh
  obtain ⟨a, ha, hnear⟩ := doubled_near_line (by norm_num : 0 < contraction)
    (by norm_num) hρ (by have := hρk; norm_num [contraction] at *; linarith)
    hu h₀ h₁ hlen hq
  rw [← affine_midpoint f x v, ← affine_residual f x v q a] at hnear
  obtain ⟨b, hb, hbnear⟩ := normalize_inverse_axis e hew hr hs hv hw hT
    (q - a • v) (x + (1 / 2 : ℝ) • v)
  have hbn : |b| ≤ 11 * ρ / contraction ^ 2 := by
    calc
      _ ≤ ‖f (q - a • v) - f (x + (1 / 2 : ℝ) • v)‖ / contraction := hb
      _ ≤ (11 * ρ / contraction) / contraction := by gcongr
      _ = _ := by ring
  refine ⟨a + b, ?_, ?_⟩
  · have hn := abs_add_le a b
    have hb' : 11 * ρ / contraction ^ 2 ≤ 11 := by
      apply (div_le_iff₀ (by norm_num : 0 < contraction ^ 2)).mpr
      linarith
    norm_num [contraction] at ha ⊢
    linarith
  · have he : q - (x + (1 / 2 : ℝ) • v) - (a + b) • v =
      q - a • v - (x + (1 / 2 : ℝ) • v) - b • v := by module
    rw [he]
    calc
      _ ≤ (7 * r / contraction) * ‖f (q - a • v) - f (x + (1 / 2 : ℝ) • v)‖ := hbnear
      _ ≤ (7 * r / contraction) * (11 * ρ / contraction) := by gcongr
      _ = _ := by ring

lemma homothety_mem_tube {x v q : Space} {a A R B : ℝ}
    (hA : |a * A| ≤ 1 / 2) (hB : ‖q - (x + (1 / 2 : ℝ) • v) - A • v‖ ≤ B)
    (hR : |a| * B < R) :
    AffineMap.homothety (x + (1 / 2 : ℝ) • v) a q ∈ tube R x v := by
  apply mem_thickening_iff.mpr
  refine ⟨x + (1 / 2 : ℝ) • v + (a * A) • v, centered_segment x v hA, ?_⟩
  rw [dist_eq_norm, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  have he : a • (q - (x + (1 / 2 : ℝ) • v)) + (x + (1 / 2 : ℝ) • v) -
      (x + (1 / 2 : ℝ) • v + (a * A) • v) =
      a • (q - (x + (1 / 2 : ℝ) • v) - A • v) := by module
  rw [he, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hB (abs_nonneg _)).trans_lt hR

lemma homothety_image_of_contraction {U V : Set Space} (p : Space) {C : ℝ} (hC : C ≠ 0)
    (h : AffineMap.homothety p C⁻¹ '' V ⊆ U) :
    V ⊆ AffineMap.homothety p C '' U := by
  intro q hq
  refine ⟨AffineMap.homothety p C⁻¹ q, h ⟨q, hq, rfl⟩, ?_⟩
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  rw [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hC, one_smul, sub_add_cancel]

lemma affine_homothety (f : Space ≃ᴬ[ℝ] Space) (p q : Space) (a : ℝ) :
    f (AffineMap.homothety p a q) = AffineMap.homothety (f p) a (f q) := by
  have h := f.toAffineEquiv.toAffineMap.apply_lineMap p q a
  change f (a • (q - p) + p) = a • (f q - f p) + f p at h
  exact h

lemma normalized_fine_expansion (e : Space ≃ₗᵢ[ℝ] Space) {y w x v z u : Space}
    (hew : e w = axis) {r s : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hR : normalizedRadius r s ≤ contraction ^ 2)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : tube s x v ⊆ tube r y w)
    (hf : normalize e y w r hr '' tube s x v ⊆ tube (normalizedRadius r s) z u) :
    tube (normalizedRadius r s) z u ⊆
      AffineMap.homothety (normalize e y w r hr (x + (1 / 2 : ℝ) • v)) dilation ''
        (normalize e y w r hr '' tube s x v) := by
  let f := normalize e y w r hr
  apply homothety_image_of_contraction _ (by norm_num [dilation, contraction] : dilation ≠ 0)
  rintro q' ⟨q, hq, rfl⟩
  let p := f.symm q
  have hfp : f p = q := f.apply_symm_apply q
  obtain ⟨A, hA, hnear⟩ := normalize_doubled_near_child e hew hr hr1 hs
    (normalizedRadius_pos hr hs) hR hv hw hu hT hf
    (q := p) (by
      rw [show normalize e y w r hr p = q from hfp]
      exact tube_subset_doubled (normalizedRadius_pos hr hs).le z u hq)
  have hh : AffineMap.homothety (x + (1 / 2 : ℝ) • v) dilation⁻¹ p ∈ tube s x v := by
    apply homothety_mem_tube (B := 77 * r * normalizedRadius r s / contraction ^ 2) ?_ hnear ?_
    · rw [abs_mul]
      have h := mul_le_mul_of_nonneg_left hA (abs_nonneg dilation⁻¹)
      norm_num [dilation, contraction] at h ⊢
      linarith
    · have he : |dilation⁻¹| * (77 * r * normalizedRadius r s / contraction ^ 2) =
          (77 / 250 : ℝ) * s := by
        norm_num [dilation, normalizedRadius, contraction, hr.ne']
        field_simp
        ring
      rw [he]
      linarith
  refine ⟨AffineMap.homothety (x + (1 / 2 : ℝ) • v) dilation⁻¹ p, hh, ?_⟩
  rw [affine_homothety, hfp]

end
end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
