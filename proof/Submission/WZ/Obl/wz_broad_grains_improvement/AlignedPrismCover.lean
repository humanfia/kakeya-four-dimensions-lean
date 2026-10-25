-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedPrismCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedCovers
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.SubprismGeometry
import Submission.WZ.Obl.wz_move_two_long_grains_gain.CrossBox
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.PrismNeighborhood

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint axisLine)
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Crosses)

set_option maxHeartbeats 800000

/-- Two tubes crossing the same thin prism lie close to one another's infinite
axes. This assertion does not require any alignment of their axial starts. -/
theorem crossing_tube_near_representative {d a ρ c : ℝ}
    (hd : 0 < d) (hda : d ≤ a) (haρ : a ≤ ρ * c)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 100) (hc1 : c ≤ 1) (h4 : 4 * d ≤ c)
    {x v y w z : V} {e : V ≃ₗᵢ[ℝ] V} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hcross : Crosses d a (ρ * c) c x v z e)
    (hrep : Crosses d a (ρ * c) c y w z e) :
    T d x v ⊆ thickening (256 * ρ) (axisLine y w) := by
  have hc : 0 < c := by linarith
  have hρc : ρ * c ≤ c := mul_le_of_le_one_left hc.le (by linarith)
  have hac : a / c ≤ ρ := (div_le_iff₀ hc).mpr haρ
  have hnear := WangZahlLot.Obl.wz_move_two_long_grains_gain.tube_subset_enlarged_box
    hv hd hda haρ hρc hc1 h4 (hcross.2 (-c/2) (by simp)) (hcross.2 (c/2) (by simp))
  have hnear' := WangZahlLot.Obl.wz_move_two_long_grains_gain.tube_subset_enlarged_box
    hw hd hda haρ hρc hc1 h4 (hrep.2 (-c/2) (by simp)) (hrep.2 (c/2) (by simp))
  have hmid : axisMidpoint y w ∈ T d y w := self_subset_thickening hd _ (by
    simpa only [axisMidpoint, zero_smul, add_zero] using
      WangZahlLot.Obl.wz_rescaled_fibre_alternatives.centered_segment y w (a := 0) (by norm_num))
  have hm := hnear' hmid
  have hwdir := hrep.narrow_direction hd hda haρ
    (by nlinarith : ρ * c ≤ c / 100) hw
  have hw0 : |e w 0| ≤ 6 * ρ :=
    hwdir.1.trans ((div_le_iff₀ hc).mpr (by nlinarith))
  have hw1 : |e w 1| ≤ 6 * ρ := by
    have hh := hwdir.2.1
    field_simp at hh
    exact hh
  have hw2 : e w 2 ≠ 0 := abs_pos.mp (by linarith [hwdir.2.2])
  intro p hp
  have hpm := hnear hp
  have hcoord (j : Fin 3) :
      e (p - axisMidpoint y w) j = e (p - z) j - e (axisMidpoint y w - z) j := by
    rw [show p - axisMidpoint y w = (p-z) - (axisMidpoint y w-z) by abel, map_sub]
    rfl
  have h0 : |e (p - axisMidpoint y w) 0| ≤ 18 * ρ := by
    rw [hcoord]
    have hh := abs_sub (e (p-z) 0) (e (axisMidpoint y w-z) 0)
    have hp0 : |e (p-z) 0| ≤ 9*(a/c) := by convert hpm.1 using 1 <;> ring
    have hm0 : |e (axisMidpoint y w-z) 0| ≤ 9*(a/c) := by convert hm.1 using 1 <;> ring
    linarith
  have h1 : |e (p - axisMidpoint y w) 1| ≤ 18 * ρ := by
    rw [hcoord]
    have hh := abs_sub (e (p-z) 1) (e (axisMidpoint y w-z) 1)
    have hp1 : |e (p-z) 1| ≤ 9*ρ := by
      convert hpm.2.1 using 1 <;> field_simp <;> ring
    have hm1 : |e (axisMidpoint y w-z) 1| ≤ 9*ρ := by
      convert hm.2.1 using 1 <;> field_simp <;> ring
    linarith
  have h2 : |e (p - axisMidpoint y w) 2| ≤ 4 := by
    rw [hcoord]
    have hp2 : |e (p-z) 2| ≤ 2 := hpm.2.2.trans_eq (by norm_num)
    have hm2 : |e (axisMidpoint y w-z) 2| ≤ 2 := hm.2.2.trans_eq (by norm_num)
    linarith [abs_sub (e (p-z) 2) (e (axisMidpoint y w-z) 2)]
  let t := e (p - axisMidpoint y w) 2 / e w 2
  have ht : |t| ≤ 8 := by
    dsimp [t]
    rw [abs_div, div_le_iff₀ (abs_pos.mpr hw2)]
    linarith [hwdir.2.2]
  let r := p - (axisMidpoint y w + t • w)
  have hrcoord (j : Fin 3) : e r j = e (p - axisMidpoint y w) j - t * e w j := by
    simp only [r, sub_add_eq_sub_sub, map_sub, map_smul, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
  have hr0 : |e r 0| ≤ 66 * ρ := by
    rw [hrcoord]
    have hprod : |t * e w 0| ≤ 8 * (6 * ρ) := by
      rw [abs_mul]
      exact mul_le_mul ht hw0 (abs_nonneg _) (by norm_num)
    linarith [abs_sub (e (p - axisMidpoint y w) 0) (t * e w 0)]
  have hr1 : |e r 1| ≤ 66 * ρ := by
    rw [hrcoord]
    have hprod : |t * e w 1| ≤ 8 * (6 * ρ) := by
      rw [abs_mul]
      exact mul_le_mul ht hw1 (abs_nonneg _) (by norm_num)
    linarith [abs_sub (e (p - axisMidpoint y w) 1) (t * e w 1)]
  have hr2 : e r 2 = 0 := by
    rw [hrcoord]
    dsimp [t]
    rw [div_mul_cancel₀ _ hw2, sub_self]
  have hrnorm : ‖r‖ < 256 * ρ := by
    have hn := EuclideanSpace.real_norm_sq_eq (e r)
    rw [Fin.sum_univ_three, hr2, e.norm_map] at hn
    have hs0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 66 * ρ)).mpr hr0
    have hs1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 66 * ρ)).mpr hr1
    rw [sq_abs] at hs0 hs1
    nlinarith [norm_nonneg r, sq_pos_of_pos hρ]
  exact mem_thickening_iff.mpr ⟨axisMidpoint y w + t • w, ⟨t, rfl⟩,
    by simpa only [dist_eq_norm] using hrnorm⟩

/-- Scalar alignment makes the common carrier of crossing fine tubes a strict
unit-length tube, with only a fixed enlargement of the prism aspect ratio. -/
theorem aligned_crossing_tube_cover {d a ρ c : ℝ}
    (hd : 0 < d) (hda : d ≤ a) (haρ : a ≤ ρ * c)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 2048) (hc1 : c ≤ 1) (h4 : 4 * d ≤ c)
    {x v y w z u : V} {e : V ≃ₗᵢ[ℝ] V} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hcap : ‖v - u‖ ≤ 1 / 10) (hcap' : ‖w - u‖ ≤ 1 / 10)
    (hmid : ‖axisMidpoint x v‖ ≤ 1)
    (halign : inner ℝ v (axisMidpoint x v) = inner ℝ w (axisMidpoint y w))
    (hcross : Crosses d a (ρ * c) c x v z e)
    (hrep : Crosses d a (ρ * c) c y w z e) :
    T d x v ⊆ T (4096 * ρ) y w := by
  have hdr : d ≤ 256 * ρ := by
    have hdc := hda.trans haρ
    have hrc := mul_le_mul_of_nonneg_left hc1 hρ.le
    nlinarith
  have hh := WangZahlLot.Obl.wz_multiscale_finite_tower.aligned_line_to_unit hd hdr
    (by linarith : 256 * ρ ≤ 1 / 8) hv hw hcap hcap' hmid halign
    (crossing_tube_near_representative hd hda haρ hρ (by linarith) hc1 h4 hv hw hcross hrep)
  simpa only [show (16 : ℝ) * (256 * ρ) = 4096 * ρ by ring] using hh

/-- The same representative carrier contains the full prism and has the axis
alignment required of a coarse carrier. -/
theorem crossing_prism_representative_carrier {d a ρ c : ℝ}
    (hd : 0 < d) (hda : d ≤ a) (haρ : a ≤ ρ * c)
    (hρ : 0 < ρ) (hc1 : c ≤ 1) (h4 : 4 * d ≤ c)
    {y w z : V} {e : V ≃ₗᵢ[ℝ] V} (hw : ‖w‖ = 1)
    (hrep : Crosses d a (ρ * c) c y w z e) :
    P a (ρ * c) c z e ⊆ T (4096 * ρ) y w ∧
      (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * (4096 * ρ)) ^ 2 := by
  have ha : 0 < a := hd.trans_le hda
  have hc : 0 < c := by linarith
  have hrc : ρ * c ≤ ρ := by nlinarith
  have hdr : d ≤ ρ := (hda.trans haρ).trans hrc
  have hsub := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.crossing_prism_subset_expanded_coarse
    (ρ := 2 * ρ) ha.le haρ (mul_pos hρ hc) hc (by linarith) e
    (thickening_mono (by linarith : d ≤ 2 * ρ) (segment ℝ y (y+w))) hrep.2
  refine ⟨hsub.trans (thickening_mono (by linarith : 2 * (2 * ρ) ≤ 4096 * ρ) _), ?_⟩
  have hdir := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.crossing_prism_direction
    e hd hda haρ h4 hw hrep.2
  have h0 : |e w 0| ≤ 6 * ρ := hdir.1.trans ((div_le_iff₀ hc).mpr (by nlinarith))
  have h1 : |e w 1| ≤ 6 * ρ := by
    have hh := hdir.2
    field_simp at hh
    exact hh
  have hs0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 6 * ρ)).mpr h0
  have hs1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 6 * ρ)).mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [sq_nonneg ρ]

end WangZahlLot.Obl.wz_broad_grains_improvement
