-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.ClusteredPhysicalGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedPhysicalGeometry

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint)
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (normalize normalizedRadius contraction coverScale buffer doubled centered_segment
    normalize_doubled_near_child tube_subset_doubled)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (axis)

set_option maxHeartbeats 800000

/-- A fixed physical midpoint cluster supplies the homothetic buffer. The
transverse error comes from the common normalized cover, so no axial alignment
or normalized midpoint identity is needed. -/
theorem clustered_physical_coarse_buffer (e : V ≃ₗᵢ[ℝ] V) {y w x v z u p q : V}
    (hew : e w = axis) {r s ρ a : ℝ} (hr : 0<r) (hr1 : r≤1) (hs : 0<s)
    (hρ : 0<ρ) (hρsmall : ρ≤1/(100*coverScale)) (ha : |a|≤buffer)
    (hv : ‖v‖=1) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (hT : T s x v ⊆ T r y w)
    (hf : normalize e y w r hr '' T s x v ⊆ T ρ z u)
    (hp : ‖p-axisMidpoint x v‖≤1/100)
    (hfp : normalize e y w r hr p ∈ T ρ z u)
    (hq : normalize e y w r hr q ∈ doubled ρ z u) :
    AffineMap.homothety p a q ∈ T (coverScale*r*ρ) x v := by
  have hρk : ρ≤contraction^2 := by
    have hh := hρsmall
    norm_num [coverScale,contraction] at hh ⊢
    linarith
  have hR : coverScale*r*ρ≤1/100 := by
    have hp := (le_div_iff₀ (by norm_num [coverScale,contraction] : 0<100*coverScale)).mp hρsmall
    have hh := mul_le_mul_of_nonneg_left hr1
      (by have := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.coverScale_pos; positivity : 0≤coverScale*ρ)
    nlinarith only [hp,hh]
  have herr : 77*r*ρ/contraction^2≤1/100 := by
    have he : 77*r*ρ/contraction^2=(77/1000000:ℝ)*(coverScale*r*ρ) := by
      unfold coverScale
      ring
    rw [he]
    linarith
  obtain ⟨A,hA,hqnear⟩ := normalize_doubled_near_child e hew hr hr1 hs hρ hρk hv hw hu hT hf hq
  obtain ⟨B,_,hpnear⟩ := normalize_doubled_near_child e hew hr hr1 hs hρ hρk hv hw hu hT hf
    (tube_subset_doubled hρ.le z u hfp)
  change ‖p-axisMidpoint x v-B•v‖≤77*r*ρ/contraction^2 at hpnear
  have hB : |B|≤1/50 := by
    have hh := norm_le_norm_add_norm_sub (p-axisMidpoint x v) (B•v)
    rw [norm_smul,Real.norm_eq_abs,hv,mul_one] at hh
    linarith
  have ha1 : |1-a|≤2 := by
    have hh := abs_sub_le 1 0 a
    norm_num at hh
    have hb : buffer≤1 := by norm_num [buffer,contraction]
    linarith
  have hcoeff : |(1-a)*B+a*A|≤1/2 := by
    calc
      _ ≤ |1-a| * |B|+|a| * |A| := by simpa only [abs_mul] using abs_add_le ((1-a)*B) (a*A)
      _ ≤ 2*(1/50)+buffer*(16/contraction) :=
        add_le_add (mul_le_mul ha1 hB (abs_nonneg _) (by norm_num))
          (mul_le_mul ha hA (abs_nonneg _) (by norm_num [buffer,contraction]))
      _ ≤ _ := by norm_num [buffer,contraction]
  apply WangZahlLot.Obl.wz_rescaled_fibre_alternatives.mem_tube_of_coordinates hcoeff
  have he : AffineMap.homothety p a q-axisMidpoint x v-((1-a)*B+a*A)•v =
      (1-a)•(p-axisMidpoint x v-B•v)+a•(q-axisMidpoint x v-A•v) := by
    simp only [AffineMap.homothety_apply,vsub_eq_sub,vadd_eq_add]
    module
  change ‖AffineMap.homothety p a q-axisMidpoint x v-((1-a)*B+a*A)•v‖<_
  rw [he]
  calc
    _ ≤ ‖(1-a)•(p-axisMidpoint x v-B•v)‖+‖a•(q-axisMidpoint x v-A•v)‖ := norm_add_le _ _
    _ = |1-a| * ‖p-axisMidpoint x v-B•v‖+|a| * ‖q-axisMidpoint x v-A•v‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ 2*(77*r*ρ/contraction^2)+buffer*(77*r*ρ/contraction^2) :=
      add_le_add (mul_le_mul ha1 hpnear (norm_nonneg _) (by norm_num))
        (mul_le_mul ha hqnear (norm_nonneg _) (by norm_num [buffer,contraction]))
    _ < _ := by
      norm_num [buffer,coverScale,contraction]
      nlinarith [mul_pos hr hρ]

/-- Normalized homothetic buffering of a common coarse carrier, around a
clustered physical midpoint. -/
theorem clustered_normalized_coarse_buffer (e : V ≃ₗᵢ[ℝ] V) {y w x v z u p : V}
    (hew : e w = axis) {r s ρ a : ℝ} (hr : 0<r) (hr1 : r≤1) (hs : 0<s)
    (hρ : 0<ρ) (hρsmall : ρ≤1/(100*coverScale)) (ha : |a|≤buffer)
    (hv : ‖v‖=1) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (hT : T s x v ⊆ T r y w)
    (hf : normalize e y w r hr '' T s x v ⊆ T ρ z u)
    (hp : ‖p-axisMidpoint x v‖≤1/100)
    (hfp : normalize e y w r hr p ∈ T ρ z u) :
    AffineMap.homothety (normalize e y w r hr p) a '' doubled ρ z u ⊆
      normalize e y w r hr '' doubled (coverScale*r*ρ) x v := by
  let f := normalize e y w r hr
  rintro q' ⟨q,hq,rfl⟩
  refine ⟨AffineMap.homothety p a (f.symm q),?_,?_⟩
  · apply tube_subset_doubled (by have := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.coverScale_pos; positivity) x v
    exact clustered_physical_coarse_buffer e hew hr hr1 hs hρ hρsmall ha hv hw hu hT hf hp hfp
      (by simpa only [show normalize e y w r hr=f from rfl,f.apply_symm_apply] using hq)
  · rw [WangZahlLot.Obl.wz_rescaled_fibre_alternatives.affine_homothety]
    change AffineMap.homothety (f p) a (f (f.symm q))=_
    rw [f.apply_symm_apply]

/-- A fixed midpoint cluster suffices for doubled physical child containment. -/
theorem clustered_child_in_physical_cover (e : V ≃ₗᵢ[ℝ] V) {y w x v x' v' z u : V}
    (hew : e w = axis) {r s ρ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1/100) (hρ : 0 < ρ)
    (hρsmall : ρ ≤ 1/(100*coverScale))
    (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hT : T s x v ⊆ T r y w)
    (hf : normalize e y w r hr '' T s x v ⊆ T ρ z u)
    (hf' : normalize e y w r hr '' T s x' v' ⊆ T ρ z u)
    (hmid : ‖axisMidpoint x' v'-axisMidpoint x v‖ ≤ 1/100) :
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
