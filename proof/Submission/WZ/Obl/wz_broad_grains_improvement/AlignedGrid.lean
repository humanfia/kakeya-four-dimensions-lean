-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedGrid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedCovers
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.NetCover

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric
open WangZahlLot.Obl.wz_multiscale_finite_tower (axisMidpoint)
open WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy (cellIdx NetSeparated mem_segment_add_iff)

set_option maxHeartbeats 800000

noncomputable def alignedCell (r : ℝ) (x v : V) : (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (cellIdx r (axisMidpoint x v), cellIdx r v)

noncomputable def alignedColor (r : ℝ) (x v : V) :
    (Fin 3 → ZMod 100000000) × (Fin 3 → ZMod 100000000) :=
  (fun j => (alignedCell r x v).1 j, fun j => (alignedCell r x v).2 j)

/-- Aligned midpoint distance is controlled by any two points of the segments
and their oriented direction distance. -/
theorem aligned_midpoint_dist_le {x v y w p q : V} (hw : ‖w‖ = 1)
    (hmid : ‖axisMidpoint x v‖ ≤ 1)
    (halign : inner ℝ v (axisMidpoint x v) = inner ℝ w (axisMidpoint y w))
    (hp : p ∈ segment ℝ x (x+v)) (hq : q ∈ segment ℝ y (y+w)) :
    ‖axisMidpoint x v - axisMidpoint y w‖ ≤ 2 * dist p q + 2 * ‖v-w‖ := by
  obtain ⟨s, hs0, hs1, rfl⟩ := mem_segment_add_iff.mp hp
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_add_iff.mp hq
  have hs : |s - 1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : axisMidpoint x v - axisMidpoint y w - (t-s) • w =
      ((x+s•v) - (y+t•w)) - (s-1/2) • (v-w) := by
    dsimp [axisMidpoint]
    module
  have hr : ‖axisMidpoint x v - axisMidpoint y w - (t-s) • w‖ ≤
      dist (x+s•v) (y+t•w) + (1/2)*‖v-w‖ := by
    rw [he, dist_eq_norm]
    have hsm : ‖(s-1/2) • (v-w)‖ ≤ (1/2)*‖v-w‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hsm)
  have hh := WangZahlLot.Obl.wz_multiscale_finite_tower.aligned_midpoint_distance hw halign (t-s)
  have hm := mul_le_mul_of_nonneg_left hmid (norm_nonneg (v-w))
  linarith

/-- All radii of tubes in the same midpoint-direction cell are comparable. -/
theorem aligned_cell_tube_subset {r s : ℝ} (hr : 0 < r) {x v y w : V}
    (hcell : alignedCell r x v = alignedCell r y w) :
    T s x v ⊆ T (s + 3*r) y w := by
  have hm := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.norm_sub_lt_of_cellIdx_eq
    hr (congrArg Prod.fst hcell)
  have hv := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.norm_sub_lt_of_cellIdx_eq
    hr (congrArg Prod.snd hcell)
  have hsm : ‖(1/2 : ℝ) • (v-w)‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  have hx : ‖x-y‖ ≤ 3*r := by
    have he : x-y = (axisMidpoint x v-axisMidpoint y w) - (1/2 : ℝ) • (v-w) := by
      dsimp [axisMidpoint]
      module
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  have hxv : ‖(x+v)-(y+w)‖ ≤ 3*r := by
    have he : (x+v)-(y+w) = (axisMidpoint x v-axisMidpoint y w) + (1/2 : ℝ) • (v-w) := by
      dsimp [axisMidpoint]
      module
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  exact WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.thickening_segment_subset_of_close hx hxv

/-- Distinct cells of one fixed colour give separated enlarged unit tubes.
The common midpoint scalar eliminates axial separation as a redundant
parameter in the positional case. -/
theorem aligned_color_separated {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 100000000)
    {x v y w u : V} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hcap : ‖v-u‖ ≤ 1/10) (hcap' : ‖w-u‖ ≤ 1/10)
    (hmid : ‖axisMidpoint x v‖ ≤ 1)
    (halign : inner ℝ v (axisMidpoint x v) = inner ℝ w (axisMidpoint y w))
    (hcolor : alignedColor r x v = alignedColor r y w)
    (hne : alignedCell r x v ≠ alignedCell r y w) :
    8000 * (10000*r) ≤ min ‖v-w‖ ‖v+w‖ ∨
      ∀ p ∈ segment ℝ x (x+v), ∀ q ∈ segment ℝ y (y+w), 2*(10000*r) ≤ dist p q := by
  have hcm (j : Fin 3) : cellIdx r (axisMidpoint x v) j % (100000000 : ℤ) =
      cellIdx r (axisMidpoint y w) j % (100000000 : ℤ) := by
    apply (ZMod.intCast_eq_intCast_iff' _ _ 100000000).mp
    exact congrFun (congrArg Prod.fst hcolor) j
  have hcv (j : Fin 3) : cellIdx r v j % (100000000 : ℤ) =
      cellIdx r w j % (100000000 : ℤ) := by
    apply (ZMod.intCast_eq_intCast_iff' _ _ 100000000).mp
    exact congrFun (congrArg Prod.snd hcolor) j
  by_cases hdir : cellIdx r v = cellIdx r w
  · right
    have hmidne : cellIdx r (axisMidpoint x v) ≠ cellIdx r (axisMidpoint y w) := by
      intro he
      exact hne (Prod.ext he hdir)
    have hfar := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.norm_sub_ge_of_cellIdx_ne
      hr (by norm_num : (1 : ℕ) ≤ 100000000) hcm hmidne
    have hclose := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.norm_sub_lt_of_cellIdx_eq hr hdir
    intro p hp q hq
    have hh := aligned_midpoint_dist_le hw hmid halign hp hq
    norm_num at hfar
    linarith
  · left
    have hfar := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.norm_sub_ge_of_cellIdx_ne
      hr (by norm_num : (1 : ℕ) ≤ 100000000) hcv hdir
    have hanti := WangZahlLot.Obl.wz_multiscale_finite_tower.norm_add_lower_of_common_direction hv hcap hcap'
    apply le_min
    · norm_num at hfar
      linarith
    · linarith

end WangZahlLot.Obl.wz_broad_grains_improvement
