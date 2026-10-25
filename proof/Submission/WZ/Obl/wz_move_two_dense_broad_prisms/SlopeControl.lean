-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.SlopeControl.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.SlopeFrame
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry

/-! Transferring prism points and nearby slopes into the selected frame. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set Metric

/-- A frame following a crossing direction keeps the old prism in a bounded
anisotropic dilation. -/
theorem prism_in_slope_frame {a b c : ℝ} (hc : 0 < c) (hab : a ≤ b) (hbc : b ≤ c)
    (e g : V ≃ₗᵢ[ℝ] V) {u : V} (hu : ‖u‖ = 1) (hu2 : e u 2 ≠ 0)
    (hg2 : ∀ p, g p 2 = inner ℝ u p)
    (hg0 : ∀ p, |g p 0| ≤ 2 * |e p 0 - (e u 0 / e u 2) * e p 2|)
    (h0 : |e u 0 / e u 2| ≤ 72*a/c) (h1 : |e u 1 / e u 2| ≤ 72*b/c)
    (z : V) : P a b c z e ⊆ P (200*a) (200*b) (2*c) z g := by
  intro p hp
  have hbound {A : ℝ} (j : Fin 3) (hjp : |e (p-z) j| ≤ A/2)
      (hju : |e u j / e u 2| ≤ 72*A/c) :
      |e (p-z) j - (e u j / e u 2) * e (p-z) 2| ≤ 73*A/2 := by
    calc
      _ ≤ |e (p-z) j| + |(e u j / e u 2) * e (p-z) 2| := abs_sub _ _
      _ = |e (p-z) j| + |e u j / e u 2| * |e (p-z) 2| := by rw [abs_mul]
      _ ≤ A/2 + (72*A/c)*(c/2) :=
        add_le_add hjp (mul_le_mul hju hp.2.2 (abs_nonneg _) (by linarith [abs_nonneg (e u j / e u 2)]))
      _ = 73*A/2 := by field_simp <;> ring
  have hb0 := hbound 0 hp.1 h0
  have hb1 := hbound 1 hp.2.1 h1
  refine ⟨?_, ?_, ?_⟩
  · have hh := hg0 (p-z)
    change |g (p-z) 0| ≤ (200*a)/2
    have ha : 0 ≤ a := by linarith [abs_nonneg (e (p-z) 0), hp.1]
    linarith
  · have hh := frame_transverse_slope_bound e g hu hu2 hg2 (p-z)
    change |g (p-z) 1| ≤ (200*b)/2
    have hb : 0 ≤ b := by linarith [abs_nonneg (e (p-z) 1), hp.2.1]
    linarith
  · have hh := wz_two_scale_flat_box_estimate.box_subset_closedBall hab hbc hc.le z e hp
    have hn : ‖p-z‖ ≤ c := by simpa only [mem_closedBall, dist_eq_norm] using hh
    have hcoord := wz_move_two_long_grains_gain.abs_coord_le_norm (g (p-z)) 2
    rw [g.norm_map] at hcoord
    change |g (p-z) 2| ≤ 2*c/2
    linarith

/-- Two close slope coordinates give the required small transverse components
in the selected frame. -/
theorem direction_in_slope_frame {s t : ℝ} (e g : V ≃ₗᵢ[ℝ] V) {u w : V}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hu2 : e u 2 ≠ 0) (hw2 : e w 2 ≠ 0)
    (hg2 : ∀ p, g p 2 = inner ℝ u p)
    (hg0 : ∀ p, |g p 0| ≤ 2 * |e p 0 - (e u 0 / e u 2) * e p 2|)
    (h0 : |e w 0 / e w 2 - e u 0 / e u 2| ≤ s)
    (h1 : |e w 1 / e w 2 - e u 1 / e u 2| ≤ t) :
    |g w 0| ≤ 2*s ∧ |g w 1| ≤ s+t := by
  have hwlong : |e w 2| ≤ 1 := by
    simpa only [e.norm_map, hw] using wz_move_two_long_grains_gain.abs_coord_le_norm (e w) 2
  have hbound {A : ℝ} (j : Fin 3) (hj : |e w j / e w 2 - e u j / e u 2| ≤ A) :
      |e w j - (e u j / e u 2) * e w 2| ≤ A := by
    have he : e w j - (e u j / e u 2) * e w 2 =
        e w 2 * (e w j / e w 2 - e u j / e u 2) := by field_simp <;> ring
    rw [he, abs_mul]
    calc
      _ ≤ 1 * A := mul_le_mul hwlong hj (abs_nonneg _) zero_le_one
      _ = A := one_mul A
  exact ⟨(hg0 w).trans (by linarith [hbound 0 h0]),
    (frame_transverse_slope_bound e g hu hu2 hg2 w).trans (add_le_add (hbound 0 h0) (hbound 1 h1))⟩

lemma abs_long_of_transverse_small (g : V ≃ₗᵢ[ℝ] V) {w : V} (hw : ‖w‖ = 1)
    (h0 : |g w 0| ≤ 1/100) (h1 : |g w 1| ≤ 1/100) : 1/2 ≤ |g w 2| := by
  have hn := EuclideanSpace.real_norm_sq_eq (g w)
  rw [Fin.sum_univ_three, g.norm_map, hw] at hn
  have hsq0 : (g w 0)^2 ≤ (1/100 : ℝ)^2 := by nlinarith [sq_abs (g w 0), abs_nonneg (g w 0)]
  have hsq1 : (g w 1)^2 ≤ (1/100 : ℝ)^2 := by nlinarith [sq_abs (g w 1), abs_nonneg (g w 1)]
  by_contra hnot
  have hlt : |g w 2| < 1/2 := lt_of_not_ge hnot
  nlinarith [sq_abs (g w 2), abs_nonneg (g w 2)]

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
