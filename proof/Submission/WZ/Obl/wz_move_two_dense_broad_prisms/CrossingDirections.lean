-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.CrossingDirections.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.CrossingSlab
import Submission.WZ.Obl.wz_move_two_long_grains_gain.CrossBox

/-! Direction estimates for a tube crossing an anisotropic prism. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric

/-- The transverse direction components of a crossing unit tube are controlled
by the corresponding aspect ratios of its prism. -/
theorem Crosses.direction_bounds {d a b c : ℝ} {x v z : V} {e : V ≃ₗᵢ[ℝ] V}
    (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc1 : c ≤ 1)
    (h4 : 4*d ≤ c) (hv : ‖v‖ = 1) (h : Crosses d a b c x v z e) :
    |e v 0| ≤ 18*a/c ∧ |e v 1| ≤ 18*b/c := by
  have hT := wz_move_two_long_grains_gain.tube_subset_enlarged_box hv hd hda hab hbc hc1 h4
    (h.2 (-c/2) (by simp)) (h.2 (c/2) (by simp))
  have hx : x ∈ T d x v := self_subset_thickening hd _ (left_mem_segment ℝ x (x+v))
  have hxv : x+v ∈ T d x v := self_subset_thickening hd _ (right_mem_segment ℝ x (x+v))
  have heq (j : Fin 3) : e v j = e (x+v-z) j - e (x-z) j := by
    have he : (x+v-z)-(x-z) = v := by abel
    have hh := congrArg (fun t : V => e t j) he
    simpa only [map_sub, PiLp.sub_apply] using hh.symm
  constructor
  · rw [heq]
    have hh := abs_sub (e (x+v-z) 0) (e (x-z) 0)
    linarith [(hT hx).1, (hT hxv).1]
  · rw [heq]
    have hh := abs_sub (e (x+v-z) 1) (e (x-z) 1)
    linarith [(hT hx).2.1, (hT hxv).2.1]

lemma Crosses.slope_bounds {d a b c : ℝ} {x v z : V} {e : V ≃ₗᵢ[ℝ] V}
    (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc1 : c ≤ 1)
    (hdc : d ≤ c/100) (hv : ‖v‖ = 1) (h : Crosses d a b c x v z e) :
    e v 2 ≠ 0 ∧ |e v 0 / e v 2| ≤ 72*a/c ∧ |e v 1 / e v 2| ≤ 72*b/c := by
  have ha : 0 < a := hd.trans_le hda
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hlong := h.long_direction hc hdc hab hbc hv
  have hdir := h.direction_bounds hd hda hab hbc hc1 (by linarith) hv
  have hpos : 0 < |e v 2| := by linarith
  refine ⟨abs_pos.mp hpos, ?_, ?_⟩
  · rw [abs_div, div_le_iff₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left hlong (by positivity : 0 ≤ 72*a/c)
    exact hdir.1.trans (by convert hmul using 1 <;> ring)
  · rw [abs_div, div_le_iff₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left hlong (by positivity : 0 ≤ 72*b/c)
    exact hdir.2.trans (by convert hmul using 1 <;> ring)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
