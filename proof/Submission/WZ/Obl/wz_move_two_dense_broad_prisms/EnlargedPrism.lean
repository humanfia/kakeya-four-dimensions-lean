-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.EnlargedPrism.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.SlopeControl
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.CrossingDirections
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.PrismCrossing

/-! A single enlarged prism for one class of nearby tube slopes. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric

/-- Capping the wide slope allows the enlarged prism to keep its prescribed
longest dimension, even when the old prism is nearly cubical. -/
def enlargedSlope (b c : ℝ) : ℝ := min (b/c) (1/1000000)

lemma enlargedSlope_pos {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    0 < enlargedSlope b c := lt_min (div_pos hb hc) (by norm_num)

lemma enlargedSlope_large_length {b c L : ℝ} (hb : 0 ≤ b) (hc : 0 < c)
    (hbc : b ≤ c) (hL : 100000000*c ≤ L) : b ≤ enlargedSlope b c * L / 100 := by
  unfold enlargedSlope
  rcases le_total (b/c) (1/1000000) with hsmall | hlarge
  · rw [min_eq_left hsmall]
    have hLc : 100*c ≤ L := by linarith
    have hh := mul_le_mul_of_nonneg_left hLc (div_nonneg hb hc.le)
    have he : (b/c)*(100*c) = 100*b := by field_simp <;> ring
    rw [he] at hh
    linarith
  · rw [min_eq_right hlarge]
    linarith

/-- Every slope class has an enlarged prism with exact crossing by all its
members. The old prism lies in the core; consequently all the members' shadings
inside the central half-length ball lie in the new prism. -/
theorem enlarged_prism_for_slope_class {d a b c L : ℝ} {x u z : V}
    (e : V ≃ₗᵢ[ℝ] V) (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc1 : c ≤ 1) (hdc : d ≤ c/100) (hL : 100000000*c ≤ L)
    (hu : ‖u‖ = 1) (hcross : Crosses d a b c x u z e) :
    d ≤ 10000*a ∧ 10000*a ≤ 10000*enlargedSlope b c*L ∧
      10000*enlargedSlope b c*L ≤ L ∧
      ∃ g : V ≃ₗᵢ[ℝ] V,
        P a b c z e ⊆ P (10000*a/10) (10000*enlargedSlope b c*L/10) (L/10) z g ∧
        ∀ (y w : V), ‖w‖ = 1 → e w 2 ≠ 0 →
          |e w 0 / e w 2 - e u 0 / e u 2| ≤ a/L →
          |e w 1 / e w 2 - e u 1 / e u 2| ≤ enlargedSlope b c →
          (∃ p ∈ T d y w ∩ P a b c z e,
            4*L ≤ dist p y ∧ 4*L ≤ dist p (y+w)) →
          Crosses d (10000*a) (10000*enlargedSlope b c*L) L y w z g ∧
          T d y w ∩ ball z (L/2) ⊆ P (10000*a) (10000*enlargedSlope b c*L) L z g := by
  have ha : 0 < a := hd.trans_le hda
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  let R := enlargedSlope b c
  have hR : 0 < R := enlargedSlope_pos hb hc
  have hRmax : R ≤ 1/1000000 := min_le_right _ _
  have hbL : b ≤ R*L/100 := enlargedSlope_large_length hb.le hc hbc hL
  have haL : a ≤ R*L := by nlinarith
  have hsL : a/L ≤ R := (div_le_iff₀ hLpos).mpr (by nlinarith)
  have hAB : 10000*a ≤ 10000*R*L := by nlinarith
  have hBC : 10000*R*L ≤ L := by nlinarith
  refine ⟨by linarith, hAB, hBC, ?_⟩
  obtain ⟨hu2, hu0, hu1⟩ := hcross.slope_bounds hd hda hab hbc hc1 hdc hu
  obtain ⟨g, hg2, hg0⟩ := frame_of_coordinate_slope e hu hu2
  have hold := prism_in_slope_frame hc hab hbc e g hu hu2 hg2 hg0 hu0 hu1 z
  have hcore : P a b c z e ⊆ P (10000*a/10) (10000*R*L/10) (L/10) z g := by
    intro p hp
    have hh := hold hp
    refine ⟨?_, ?_, ?_⟩
    · change |g (p-z) 0| ≤ 10000*a/10/2
      linarith [hh.1]
    · change |g (p-z) 1| ≤ 10000*R*L/10/2
      linarith [hh.2.1]
    · change |g (p-z) 2| ≤ L/10/2
      linarith [hh.2.2]
  refine ⟨g, hcore, ?_⟩
  intro y w hw hw2 hs0 hs1 hmeet
  obtain ⟨p, hp, hpleft, hpright⟩ := hmeet
  have hdir := direction_in_slope_frame e g hu hw hu2 hw2 hg2 hg0 hs0 hs1
  have hwlong := abs_long_of_transverse_small g hw
    (by linarith [hdir.1]) (by linarith [hdir.2])
  have hdir0 : L * |g w 0| ≤ 10000*a/100 := by
    have hh := mul_le_mul_of_nonneg_left hdir.1 hLpos.le
    have he : L*(2*(a/L)) = 2*a := by field_simp <;> ring
    rw [he] at hh
    linarith
  have hdir1 : L * |g w 1| ≤ 10000*R*L/100 := by
    have hh := mul_le_mul_of_nonneg_left hdir.2 hLpos.le
    have he : L*(a/L+R) = a+L*R := by field_simp <;> ring
    rw [he] at hh
    nlinarith
  have hout := prism_crosses_of_core_abs hd (by positivity) hAB hBC (by linarith)
    g hw hwlong hdir0 hdir1 hp.1 (hcore hp.2) hpleft hpright
  exact ⟨hout, hout.ball_subset hLpos⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
