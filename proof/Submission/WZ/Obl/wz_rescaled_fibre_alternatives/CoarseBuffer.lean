-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.CoarseBuffer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.CoarseGeometry

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

noncomputable section

lemma mem_tube_of_coordinates {x v q : Space} {A R : ℝ}
    (hA : |A| ≤ 1 / 2) (hR : ‖q - (x + (1 / 2 : ℝ) • v) - A • v‖ < R) :
    q ∈ tube R x v := by
  apply mem_thickening_iff.mpr
  refine ⟨x + (1 / 2 : ℝ) • v + A • v, centered_segment x v hA, ?_⟩
  simpa only [dist_eq_norm, ← sub_sub] using hR

lemma physical_coarse_buffer (e : Space ≃ₗᵢ[ℝ] Space) {y w x v z u p q : Space}
    (hew : e w = axis) {r s ρ a : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hρ : 0 < ρ) (hρk : ρ ≤ contraction ^ 2) (ha : |a| ≤ buffer)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : tube s x v ⊆ tube r y w)
    (hf : normalize e y w r hr '' tube s x v ⊆ tube ρ z u)
    (hp : ‖normalize e y w r hr p - normalize e y w r hr (x + (1 / 2 : ℝ) • v)‖ ≤ 6 * ρ)
    (hq : normalize e y w r hr q ∈ doubled ρ z u) :
    AffineMap.homothety p a q ∈ tube (coverScale * r * ρ) x v := by
  let f := normalize e y w r hr
  let m := x + (1 / 2 : ℝ) • v
  obtain ⟨A, hA, hqnear⟩ := normalize_doubled_near_child e hew hr hr1 hs hρ hρk hv hw hu hT hf hq
  obtain ⟨B, hB, hpnear⟩ := normalize_inverse_axis e hew hr hs hv hw hT p m
  have hB' : |B| ≤ 6 * ρ / contraction := hB.trans
    ((div_le_div_iff_of_pos_right (by norm_num : 0 < contraction)).mpr hp)
  have hpnear' : ‖p - m - B • v‖ ≤ 42 * r * ρ / contraction := by
    calc
      _ ≤ (7 * r / contraction) * ‖f p - f m‖ := hpnear
      _ ≤ (7 * r / contraction) * (6 * ρ) := by gcongr
      _ = _ := by ring
  have ha1 : |1 - a| ≤ 2 := by
    have hh := abs_sub_le 1 0 a
    norm_num at hh
    have hb1 : buffer ≤ 1 := by norm_num [buffer, contraction]
    linarith
  have hcoeff : |(1 - a) * B + a * A| ≤ 1 / 2 := by
    calc
      _ ≤ |1 - a| * |B| + |a| * |A| := by simpa only [abs_mul] using abs_add_le ((1 - a) * B) (a * A)
      _ ≤ 2 * (6 * ρ / contraction) + buffer * (16 / contraction) :=
        add_le_add (mul_le_mul ha1 hB' (abs_nonneg _) (by norm_num))
          (mul_le_mul ha hA (abs_nonneg _) buffer_pos.le)
      _ ≤ _ := by
        norm_num [buffer, contraction] at hρk ⊢
        linarith
  apply mem_tube_of_coordinates hcoeff
  have he : AffineMap.homothety p a q - m - ((1 - a) * B + a * A) • v =
      (1 - a) • (p - m - B • v) + a • (q - m - A • v) := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  change ‖AffineMap.homothety p a q - m - ((1 - a) * B + a * A) • v‖ < _
  rw [he]
  calc
    _ ≤ ‖(1 - a) • (p - m - B • v)‖ + ‖a • (q - m - A • v)‖ := norm_add_le _ _
    _ = |1 - a| * ‖p - m - B • v‖ + |a| * ‖q - m - A • v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 2 * (42 * r * ρ / contraction) + buffer * (77 * r * ρ / contraction ^ 2) :=
      add_le_add (mul_le_mul ha1 hpnear' (norm_nonneg _) (by norm_num))
        (mul_le_mul ha hqnear (norm_nonneg _) buffer_pos.le)
    _ < _ := by
      norm_num [buffer, coverScale, contraction]
      nlinarith [mul_pos hr hρ]

lemma normalized_coarse_buffer (e : Space ≃ₗᵢ[ℝ] Space) {y w x v z u p : Space}
    (hew : e w = axis) {r s ρ a : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hρ : 0 < ρ) (hρk : ρ ≤ contraction ^ 2) (ha : |a| ≤ buffer)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : tube s x v ⊆ tube r y w)
    (hf : normalize e y w r hr '' tube s x v ⊆ tube ρ z u)
    (hp : ‖normalize e y w r hr p - normalize e y w r hr (x + (1 / 2 : ℝ) • v)‖ ≤ 6 * ρ) :
    AffineMap.homothety (normalize e y w r hr p) a '' doubled ρ z u ⊆
      normalize e y w r hr '' doubled (coverScale * r * ρ) x v := by
  let f := normalize e y w r hr
  rintro q' ⟨q, hq, rfl⟩
  refine ⟨AffineMap.homothety p a (f.symm q), ?_, ?_⟩
  · apply tube_subset_doubled (by have := coverScale_pos; positivity) x v
    exact physical_coarse_buffer e hew hr hr1 hs hρ hρk ha hv hw hu hT hf hp
      (by simpa only [show normalize e y w r hr = f from rfl, f.apply_symm_apply] using hq)
  · rw [affine_homothety]
    change AffineMap.homothety (f p) a (f (f.symm q)) = _
    rw [f.apply_symm_apply]

lemma doubled_tube_volume_upper {R : ℝ} (hR : 0 ≤ R) (hR1 : 2 * R ≤ 1)
    (x v : Space) (hv : ‖v‖ = 1) :
    volume (doubled R x v) ≤ ENNReal.ofReal (448 * R ^ 2) := by
  have hsub : doubled R x v ⊆
      tube (2 * R) (x - (1 / 2 : ℝ) • v) v ∪ tube (2 * R) (x + (1 / 2 : ℝ) • v) v := by
    intro q hq
    obtain ⟨p, hp, hqp⟩ := mem_thickening_iff.mp hq
    rw [segment_eq_image'] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    simp only [add_sub_cancel_left] at hqp
    by_cases ht' : t ≤ 1 / 2
    · left
      apply mem_thickening_iff.mpr
      refine ⟨x - (1 / 2 : ℝ) • v + t • (2 • v), ?_, hqp⟩
      rw [segment_eq_image']
      refine ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, ?_⟩
      simp only [add_sub_cancel_left]
      module
    · right
      apply mem_thickening_iff.mpr
      refine ⟨x - (1 / 2 : ℝ) • v + t • (2 • v), ?_, hqp⟩
      rw [segment_eq_image']
      refine ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩, ?_⟩
      simp only [add_sub_cancel_left]
      module
  have hu₀ := WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper
    (by positivity : 0 ≤ 2 * R) hR1 (x - (1 / 2 : ℝ) • v) v hv
  have hu₁ := WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper
    (by positivity : 0 ≤ 2 * R) hR1 (x + (1 / 2 : ℝ) • v) v hv
  calc
    _ ≤ volume (tube (2 * R) (x - (1 / 2 : ℝ) • v) v) +
        volume (tube (2 * R) (x + (1 / 2 : ℝ) • v) v) := (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (56 * (2 * R) ^ 2) + ENNReal.ofReal (56 * (2 * R) ^ 2) := add_le_add hu₀ hu₁
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

lemma coarse_volume_comparison (e : Space ≃ₗᵢ[ℝ] Space) (y w x v z u : Space)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hR1 : 2 * (coverScale * r * ρ) ≤ 1)
    (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    volume (normalize e y w r hr '' doubled (coverScale * r * ρ) x v) ≤
      ENNReal.ofReal (448 * coverScale ^ 2 * contraction ^ 3) * volume (doubled ρ z u) := by
  have hscale := coverScale_pos
  have hlo := (WangZahlLot.Obl.wz_direction_density_transfer.tube_volume_lower hρ z u hu).trans
    (measure_mono (tube_subset_doubled hρ.le z u))
  rw [normalize_volume]
  calc
    _ ≤ ENNReal.ofReal (jacobian r) * ENNReal.ofReal (448 * (coverScale * r * ρ) ^ 2) :=
      mul_le_mul_right (doubled_tube_volume_upper (by positivity) hR1 x v hv) _
    _ = ENNReal.ofReal (448 * coverScale ^ 2 * contraction ^ 3) * ENNReal.ofReal (ρ ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold jacobian
      field_simp
    _ ≤ _ := mul_le_mul_right hlo _

end
end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
