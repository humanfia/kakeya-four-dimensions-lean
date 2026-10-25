-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.PrismCrossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_broad_grains_initialization.CubeGeometry
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormDefs

/-! Exact crossing of anisotropic prisms, using the accepted cube crossing API. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set Metric
open wz_broad_grains_initialization (cube mem_cube_iff cube_parameter_close
  tube_axis_coord_error tube_cube_crosses)

/-- The short coordinates stay strictly inside the prism if its direction is
sufficiently close to the long axis relative to each short side. -/
lemma short_coordinate_of_core {d c A : ℝ} (hc : 0 < c) (hA : 0 < A)
    (hdA : d ≤ A / 100) (hdc : d ≤ c / 100)
    {x v z p q : V} (e : V ≃ₗᵢ[ℝ] V) (hvlong : 1 / 2 ≤ e v 2)
    (hpT : p ∈ T d x v) (hp : p ∈ cube (c / 10) z e)
    (hqT : q ∈ T d x v) (hq : q ∈ cube c z e)
    (j : Fin 3) (hvp : c * |e v j| ≤ A / 100)
    (hpp : |e (p-z) j| ≤ A / 20) : |e (q-z) j| < A / 2 := by
  obtain ⟨s, _, hs⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hpT
  obtain ⟨t, _, ht⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hqT
  have hst := cube_parameter_close hc hdc e hvlong hp hq hs ht
  have herrp := tube_axis_coord_error e hs (z := z) j
  have herrq := tube_axis_coord_error e ht (z := z) j
  have hmove : |(t-s) * e v j| ≤ A / 50 := by
    rw [abs_mul]
    have hmul := mul_le_mul_of_nonneg_right hst (abs_nonneg (e v j))
    linarith
  have he : e (q-z) j =
      (e (q-z) j - (e (x-z) j + t * e v j)) +
      e (p-z) j + (t-s) * e v j -
      (e (p-z) j - (e (x-z) j + s * e v j)) := by ring
  calc
    |e (q-z) j| ≤ |e (q-z) j - (e (x-z) j + t * e v j)| +
        |e (p-z) j| + |(t-s) * e v j| +
        |e (p-z) j - (e (x-z) j + s * e v j)| := by
      conv_lhs => rw [he]
      have h₁ := abs_add_le (e (q-z) j - (e (x-z) j + t * e v j)) (e (p-z) j)
      have h₂ := abs_add_le ((e (q-z) j - (e (x-z) j + t * e v j)) + e (p-z) j)
        ((t-s) * e v j)
      have h₃ := abs_sub ((e (q-z) j - (e (x-z) j + t * e v j)) +
        e (p-z) j + (t-s) * e v j) (e (p-z) j - (e (x-z) j + s * e v j))
      linarith
    _ < A / 2 := by linarith

/-- A strict coordinate box is an open subset of the closed prism. -/
lemma strict_box_mem_interior {a b c : ℝ} {z p : V} {e : V ≃ₗᵢ[ℝ] V}
    (h0 : |e (p-z) 0| < a / 2) (h1 : |e (p-z) 1| < b / 2)
    (h2 : |e (p-z) 2| < c / 2) : p ∈ interior (P a b c z e) := by
  let U : Set V := {q | |e (q-z) 0| < a / 2} ∩
    ({q | |e (q-z) 1| < b / 2} ∩ {q | |e (q-z) 2| < c / 2})
  have hU : IsOpen U :=
    (isOpen_lt (by fun_prop) continuous_const).inter
      ((isOpen_lt (by fun_prop) continuous_const).inter
        (isOpen_lt (by fun_prop) continuous_const))
  have hsub : U ⊆ P a b c z e := fun q hq => ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩
  exact interior_maximal hsub hU ⟨h0, h1, h2⟩

/-- The entire fine tube crosses the prism through its two long faces.
The core point is away from the fine tube endpoints. -/
theorem prism_crosses_of_core {d a b c : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (hda : d ≤ a / 100)
    {x v z p : V} (e : V ≃ₗᵢ[ℝ] V) (hv : ‖v‖ = 1)
    (hvlong : 1 / 2 ≤ e v 2)
    (hv0 : c * |e v 0| ≤ a / 100) (hv1 : c * |e v 1| ≤ b / 100)
    (hpT : p ∈ T d x v) (hp : p ∈ P (a / 10) (b / 10) (c / 10) z e)
    (hleft : 4 * c ≤ dist p x) (hright : 4 * c ≤ dist p (x+v)) :
    Crosses d a b c x v z e := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hdc : d ≤ c / 100 := by linarith
  have hpCube : p ∈ cube (c / 10) z e := by
    apply mem_cube_iff.mpr
    intro j
    fin_cases j
    · change |e (p-z) 0| ≤ _
      have hp0 : |e (p-z) 0| ≤ a / 10 / 2 := hp.1
      linarith
    · change |e (p-z) 1| ≤ _
      have hp1 : |e (p-z) 1| ≤ b / 10 / 2 := hp.2.1
      linarith
    · exact hp.2.2
  have hboxCube : P a b c z e ⊆ cube c z e := by
    intro q hq
    apply mem_cube_iff.mpr
    intro j
    fin_cases j
    · change |e (q-z) 0| ≤ _
      have hq0 : |e (q-z) 0| ≤ a / 2 := hq.1
      linarith
    · change |e (q-z) 1| ≤ _
      have hq1 : |e (q-z) 1| ≤ b / 2 := hq.2.1
      linarith
    · exact hq.2.2
  have hshort0 {q : V} (hqT : q ∈ T d x v) (hq : q ∈ cube c z e) :
      |e (q-z) 0| < a / 2 := short_coordinate_of_core hc ha hda hdc e hvlong
        hpT hpCube hqT hq 0 hv0 (by linarith [hp.1])
  have hshort1 {q : V} (hqT : q ∈ T d x v) (hq : q ∈ cube c z e) :
      |e (q-z) 1| < b / 2 := short_coordinate_of_core hc hb (by linarith) hdc e hvlong
        hpT hpCube hqT hq 1 hv1 (by linarith [hp.2.1])
  constructor
  · intro q hq
    have hqBox : q ∈ P a b c z e :=
      (wz_two_scale_flat_box_estimate.box_isClosed a b c z e).frontier_subset hq.2
    apply le_antisymm hqBox.2.2
    by_contra hlt
    exact hq.2.2 (strict_box_mem_interior (hshort0 hq.1 (hboxCube hqBox))
      (hshort1 hq.1 (hboxCube hqBox)) (lt_of_not_ge hlt))
  · have hvshort : ∀ j : Fin 3, j ≠ 2 → |e v j| ≤ 1 / 100 := by
      intro j hj
      fin_cases j
      · change |e v 0| ≤ _
        nlinarith
      · change |e v 1| ≤ _
        nlinarith
      · exact (hj rfl).elim
    intro t ht
    obtain ⟨q, ⟨hqT, hqCube⟩, hqt⟩ := tube_cube_crosses hc hd hdc e hv hvlong hvshort
      hpT hpCube hleft hright t ht
    exact ⟨q, ⟨hqT, (hshort0 hqT hqCube).le, (hshort1 hqT hqCube).le,
      mem_cube_iff.mp hqCube 2⟩, hqt⟩

/-- The crossing criterion is independent of the chosen orientation of the
fine segment. -/
theorem prism_crosses_of_core_abs {d a b c : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (hda : d ≤ a / 100)
    {x v z p : V} (e : V ≃ₗᵢ[ℝ] V) (hv : ‖v‖ = 1)
    (hvlong : 1 / 2 ≤ |e v 2|)
    (hv0 : c * |e v 0| ≤ a / 100) (hv1 : c * |e v 1| ≤ b / 100)
    (hpT : p ∈ T d x v) (hp : p ∈ P (a / 10) (b / 10) (c / 10) z e)
    (hleft : 4 * c ≤ dist p x) (hright : 4 * c ≤ dist p (x+v)) :
    Crosses d a b c x v z e := by
  by_cases hvpos : 0 ≤ e v 2
  · exact prism_crosses_of_core hd ha hab hbc hda e hv
      (by rwa [abs_of_nonneg hvpos] at hvlong) hv0 hv1 hpT hp hleft hright
  · have hrev : T d (x+v) (-v) = T d x v :=
      wz_extremal_lipschitz_grains.tube_reverse d x v
    have hneg := prism_crosses_of_core hd ha hab hbc hda e
      (v := -v) (x := x+v) (by simpa using hv)
      (by simpa only [map_neg, PiLp.neg_apply, abs_of_neg (lt_of_not_ge hvpos)] using hvlong)
      (by simpa only [map_neg, PiLp.neg_apply, abs_neg] using hv0)
      (by simpa only [map_neg, PiLp.neg_apply, abs_neg] using hv1)
      (by rwa [hrev]) hp hright (by simpa only [add_neg_cancel_right] using hleft)
    simpa only [Crosses, hrev] using hneg

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
