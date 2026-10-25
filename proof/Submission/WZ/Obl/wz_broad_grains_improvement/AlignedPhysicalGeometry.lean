-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedPhysicalGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedCovers
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.CoarseBuffer

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_multiscale_finite_tower
  (axisMidpoint unit_near_multiple aligned_midpoint_distance norm_add_lower_of_common_direction)
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (normalize normalizedRadius contraction coverScale buffer doubled centered_segment
    normalize_doubled_near_child tube_subset_doubled)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

set_option maxHeartbeats 800000

/-- For physically aligned unit axes, closeness to the representative line
controls the full midpoint displacement. -/
theorem aligned_midpoint_of_near_axis {s b : ℝ} (hs : 0 < s) {x v x' v' u : V}
    (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hvu : ‖v-u‖ ≤ 1/10) (hv'u : ‖v'-u‖ ≤ 1/10)
    (hmid : ‖axisMidpoint x' v'‖ ≤ 1)
    (halign : inner ℝ v' (axisMidpoint x' v') = inner ℝ v (axisMidpoint x v))
    (hnear : ∀ p ∈ T s x' v', ∃ a : ℝ, ‖p-axisMidpoint x v-a•v‖ ≤ b) :
    ‖axisMidpoint x' v'-axisMidpoint x v‖ ≤ 6*b := by
  obtain ⟨a₀,ha₀⟩ := hnear x' (self_subset_thickening hs _ (left_mem_segment ℝ _ _))
  obtain ⟨a₁,ha₁⟩ := hnear (x'+v') (self_subset_thickening hs _ (right_mem_segment ℝ _ _))
  obtain ⟨am,ham⟩ := hnear (axisMidpoint x' v') (self_subset_thickening hs _
    (by simpa only [axisMidpoint,zero_smul,add_zero] using
      centered_segment x' v' (a := 0) (by norm_num)))
  have hvnear : ‖v'-(a₁-a₀)•v‖ ≤ 2*b := by
    have he : v'-(a₁-a₀)•v =
      ((x'+v')-axisMidpoint x v-a₁•v) - (x'-axisMidpoint x v-a₀•v) := by module
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  have hsub : ‖v'-v‖ ≤ 1/5 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub v' u v
    rw [norm_sub_rev u v] at hh
    linarith
  have hsum : 1 ≤ ‖v'+v‖ := norm_add_lower_of_common_direction hv' hv'u hvu
  have hang := unit_near_multiple hv' hv (a₁-a₀)
  rw [min_eq_left (hsub.trans (by linarith))] at hang
  have hang' : ‖v'-v‖ ≤ 4*b := by linarith
  have hm := aligned_midpoint_distance hv halign am
  have hm' : ‖v'-v‖*‖axisMidpoint x' v'‖ ≤ 4*b :=
    (mul_le_mul_of_nonneg_left hmid (norm_nonneg _)).trans (by simpa using hang')
  linarith

/-- A common normalized coarse cover controls physical midpoints whenever the
physical axes are aligned. Normalized extension midpoints may be shifted. -/
theorem aligned_physical_midpoints_close (e : V ≃ₗᵢ[ℝ] V) {y w x v x' v' z u u₀ : V}
    (hew : e w = axis) {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hρ : 0 < ρ) (hρk : ρ ≤ contraction^2)
    (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hvu : ‖v-u₀‖ ≤ 1/10) (hv'u : ‖v'-u₀‖ ≤ 1/10)
    (hmid : ‖axisMidpoint x' v'‖ ≤ 1)
    (halign : inner ℝ v' (axisMidpoint x' v') = inner ℝ v (axisMidpoint x v))
    (hT : T s x v ⊆ T r y w)
    (hf : normalize e y w r hr '' T s x v ⊆ T ρ z u)
    (hf' : normalize e y w r hr '' T s x' v' ⊆ T ρ z u) :
    ‖axisMidpoint x' v'-axisMidpoint x v‖ ≤ 462*r*ρ/contraction^2 := by
  have hh := aligned_midpoint_of_near_axis hs hv hv' hvu hv'u hmid halign
    (b := 77*r*ρ/contraction^2) (by
      intro p hp
      obtain ⟨a,_,ha⟩ := normalize_doubled_near_child e hew hr hr1 hs hρ hρk
        hv hw hu hT hf (tube_subset_doubled hρ.le z u (hf' ⟨p,hp,rfl⟩))
      exact ⟨a,ha⟩)
  convert hh using 1 <;> ring

/-- A small physical midpoint displacement provides the homothetic buffer used
by the slab comparison, without an exact normalized-midpoint identity. -/
theorem aligned_physical_coarse_buffer (e : V ≃ₗᵢ[ℝ] V) {y w x v z u p q : V}
    (hew : e w = axis) {r s ρ a : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hρ : 0 < ρ) (hρk : ρ ≤ contraction^2) (ha : |a| ≤ buffer)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : T s x v ⊆ T r y w)
    (hf : normalize e y w r hr '' T s x v ⊆ T ρ z u)
    (hp : ‖p-axisMidpoint x v‖ ≤ 462*r*ρ/contraction^2)
    (hq : normalize e y w r hr q ∈ doubled ρ z u) :
    AffineMap.homothety p a q ∈ T (coverScale*r*ρ) x v := by
  obtain ⟨A,hA,hnear⟩ := normalize_doubled_near_child e hew hr hr1 hs hρ hρk hv hw hu hT hf hq
  have ha1 : |1-a| ≤ 2 := by
    have hh := abs_sub_le 1 0 a
    norm_num at hh
    have hb : buffer ≤ 1 := by norm_num [buffer,contraction]
    linarith
  have hcoeff : |a*A| ≤ 1/2 := by
    rw [abs_mul]
    have hh := mul_le_mul ha hA (abs_nonneg _) (by norm_num [buffer,contraction] : 0 ≤ buffer)
    norm_num [buffer,contraction] at hh ⊢
    linarith
  apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.mem_tube_of_coordinates hcoeff
  have he : AffineMap.homothety p a q-axisMidpoint x v-(a*A)•v =
      (1-a)•(p-axisMidpoint x v)+a•(q-axisMidpoint x v-A•v) := by
    simp only [AffineMap.homothety_apply,vsub_eq_sub,vadd_eq_add]
    module
  change ‖AffineMap.homothety p a q-axisMidpoint x v-(a*A)•v‖ < _
  rw [he]
  calc
    _ ≤ ‖(1-a)•(p-axisMidpoint x v)‖+‖a•(q-axisMidpoint x v-A•v)‖ := norm_add_le _ _
    _ = |1-a| * ‖p-axisMidpoint x v‖+|a| * ‖q-axisMidpoint x v-A•v‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ 2*(462*r*ρ/contraction^2)+buffer*(77*r*ρ/contraction^2) :=
      add_le_add (mul_le_mul ha1 hp (norm_nonneg _) (by norm_num))
        (mul_le_mul ha hnear (norm_nonneg _) (by norm_num [buffer,contraction]))
    _ < _ := by
      norm_num [buffer,coverScale,contraction]
      nlinarith [mul_pos hr hρ]



/-- The normalized buffer for physically aligned fine axes. -/
theorem aligned_normalized_coarse_buffer (e : V ≃ₗᵢ[ℝ] V) {y w x v z u p : V}
    (hew : e w = axis) {r s ρ a : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s)
    (hρ : 0 < ρ) (hρk : ρ ≤ contraction^2) (ha : |a| ≤ buffer)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : T s x v ⊆ T r y w)
    (hf : normalize e y w r hr '' T s x v ⊆ T ρ z u)
    (hp : ‖p-axisMidpoint x v‖ ≤ 462*r*ρ/contraction^2) :
    AffineMap.homothety (normalize e y w r hr p) a '' doubled ρ z u ⊆
      normalize e y w r hr '' doubled (coverScale*r*ρ) x v := by
  let f := normalize e y w r hr
  rintro q' ⟨q,hq,rfl⟩
  refine ⟨AffineMap.homothety p a (f.symm q),?_,?_⟩
  · apply tube_subset_doubled (by have := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.coverScale_pos; positivity) x v
    exact aligned_physical_coarse_buffer e hew hr hr1 hs hρ hρk ha hv hw hu hT hf hp
      (by simpa only [show normalize e y w r hr = f from rfl,f.apply_symm_apply] using hq)
  · rw [WangZahlLot.Obl.wz_rescaled_fibre_alternatives.affine_homothety]
    change AffineMap.homothety (f p) a (f (f.symm q)) = _
    rw [f.apply_symm_apply]

/-- Transport the physical child using the midpoint bound obtained from
physical alignment. No midpoint of a normalized unit extension occurs. -/
theorem aligned_child_in_physical_cover (e : V ≃ₗᵢ[ℝ] V) {y w x v x' v' z u : V}
    (hew : e w = axis) {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1/100) (hρ : 0 < ρ)
    (hρsmall : ρ ≤ 1/(100*coverScale))
    (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : T s x v ⊆ T r y w)
    (hf : normalize e y w r hr '' T s x v ⊆ T ρ z u)
    (hf' : normalize e y w r hr '' T s x' v' ⊆ T ρ z u)
    (hmid : ‖axisMidpoint x' v'-axisMidpoint x v‖ ≤ 462*r*ρ/contraction^2) :
    T s x' v' ⊆ doubled (coverScale*r*ρ) x v := by
  have hρk : ρ ≤ contraction^2 := by
    have hh := hρsmall
    norm_num [coverScale,contraction] at hh ⊢
    linarith
  have hR : coverScale*r*ρ ≤ 1/100 := by
    have hp := (le_div_iff₀ (by norm_num [coverScale,contraction] : 0 < 100*coverScale)).mp hρsmall
    have hh := mul_le_mul_of_nonneg_left hr1
      (by have := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.coverScale_pos; positivity : 0 ≤ coverScale*ρ)
    nlinarith only [hp,hh]
  have herr : 77*r*ρ/contraction^2 < 1/100 := by
    have he : 77*r*ρ/contraction^2 = (77/1000000:ℝ)*(coverScale*r*ρ) := by
      unfold coverScale
      ring
    rw [he]
    linarith
  have hmid' : ‖axisMidpoint x' v'-axisMidpoint x v‖ ≤ 1/100 := by
    have he : 462*r*ρ/contraction^2 = (462/1000000:ℝ)*(coverScale*r*ρ) := by
      unfold coverScale
      ring
    rw [he] at hmid
    linarith
  intro q hq
  obtain ⟨A,_,hnear⟩ := normalize_doubled_near_child e hew hr hr1 hs hρ hρk hv hw hu hT hf
    (tube_subset_doubled hρ.le z u (hf' ⟨q,hq,rfl⟩))
  change ‖q-axisMidpoint x v-A•v‖ ≤ 77*r*ρ/contraction^2 at hnear
  have hdist : ‖q-axisMidpoint x v‖ < s+1/2+1/100 := by
    have hh := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.tube_dist_midpoint hv' hq
    simp only [dist_eq_norm] at hh
    change ‖q-axisMidpoint x' v'‖ < s+1/2 at hh
    have hn := norm_sub_le_norm_sub_add_norm_sub q (axisMidpoint x' v') (axisMidpoint x v)
    linarith
  have hnorm : |A| ≤ 1 := by
    have hn := norm_le_norm_add_norm_sub (q-axisMidpoint x v) (A•v)
    rw [norm_smul,Real.norm_eq_abs,hv,mul_one] at hn
    linarith
  apply mem_thickening_iff.mpr
  refine ⟨axisMidpoint x v+A•v,
    WangZahlLot.Obl.wz_rescaled_fibre_alternatives.centered_doubled_segment x v hnorm,?_⟩
  rw [dist_eq_norm,← sub_sub]
  apply hnear.trans_lt
  norm_num [coverScale,contraction]
  nlinarith [mul_pos hr hρ]

end WangZahlLot.Obl.wz_broad_grains_improvement
