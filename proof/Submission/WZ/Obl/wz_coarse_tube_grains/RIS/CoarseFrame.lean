-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CoarseFrame.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.GrainCrossing

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open LeanEval.Analysis.WangZahlKakeya Set Metric

/-- A transverse coordinate of a covered coarse axis is controlled by the
same coordinate of the fine axis. -/
theorem covered_coarse_coordinate_bound {δ ρ : ℝ} {x v y w : V}
    (hδ : 0 < δ) (hρ4 : ρ ≤ 1 / 4)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (e : V ≃ₗᵢ[ℝ] V) (i : Fin 3)
    (hcover : T δ x v ⊆ T ρ y w) (hi : |e v i| ≤ ρ) : |e w i| ≤ 6 * ρ := by
  have hx : x ∈ T ρ y w :=
    hcover (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hxv : x + v ∈ T ρ y w :=
    hcover (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  obtain ⟨s, -, hs⟩ := tube_two_point_error hxv hx
  simp only [add_sub_cancel_left] at hs
  have hnorm : 1 ≤ ‖v - s • w‖ + |s| := by
    have h := norm_add_le (v - s • w) (s • w)
    rw [sub_add_cancel, hv, norm_smul, Real.norm_eq_abs, hw, mul_one] at h
    exact h
  have hslo : 1 / 2 ≤ |s| := by linarith
  have hcoord : |e v i - s * e w i| < 2 * ρ := by
    have h := (abs_rotated_coord_le e (v - s • w) i).trans_lt hs
    simpa only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using h
  have h := abs_sub (e v i) (e v i - s * e w i)
  rw [sub_sub_cancel, abs_mul] at h
  have hlo := mul_le_mul_of_nonneg_right hslo (abs_nonneg (e w i))
  linarith

/-- A unit coarse axis covering a nearly axial fine unit tube has the frame
alignment required of a grain in the frozen statement. -/
theorem coarse_axis_frame_bound {δ ρ : ℝ} {x v y w : V}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (e : V ≃ₗᵢ[ℝ] V)
    (hcover : T δ x v ⊆ T ρ y w)
    (h0 : |e v 0| ≤ ρ) (h1 : |e v 1| ≤ ρ) :
    (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2 := by
  have h0' := covered_coarse_coordinate_bound hδ hρ4 hv hw e 0 hcover h0
  have h1' := covered_coarse_coordinate_bound hδ hρ4 hv hw e 1 hcover h1
  have hw0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 6 * ρ)).mpr h0'
  have hw1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 6 * ρ)).mpr h1'
  simp only [sq_abs] at hw0 hw1
  nlinarith [sq_nonneg ρ]

/-- The short-direction inequalities used for the prism crossing construction
imply the frozen coarse-axis alignment when b<=rho*c. -/
theorem coarse_axis_frame_bound_of_prism_directions {δ ρ a b c : ℝ} {x v y w : V}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hc : 0 < c)
    (hab : a ≤ b) (hb : b ≤ ρ * c)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (e : V ≃ₗᵢ[ℝ] V)
    (hcover : T δ x v ⊆ T ρ y w)
    (h0 : c * |e v 0| ≤ a / 16) (h1 : c * |e v 1| ≤ b / 16) :
    (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2 := by
  apply coarse_axis_frame_bound hδ hρ hρ4 hv hw e hcover
  · apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith [mul_pos hρ hc]
  · apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith [mul_pos hρ hc]

/-- Every covered fine axis inherits a transverse coordinate bound from its
coarse unit segment, with an additional twice-radius error. -/
theorem covered_fine_coordinate_bound {δ ρ B : ℝ} {x v y w : V}
    (hδ : 0 < δ) (e : V ≃ₗᵢ[ℝ] V) (i : Fin 3)
    (hcover : T δ x v ⊆ T ρ y w) (hi : |e w i| ≤ B) : |e v i| ≤ B + 2 * ρ := by
  have hx : x ∈ T ρ y w :=
    hcover (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v)))
  have hxv : x + v ∈ T ρ y w :=
    hcover (self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v)))
  obtain ⟨s, hs1, hs⟩ := tube_two_point_error hxv hx
  simp only [add_sub_cancel_left] at hs
  have hcoord : |e v i - s * e w i| < 2 * ρ := by
    have h := (abs_rotated_coord_le e (v - s • w) i).trans_lt hs
    simpa only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using h
  have h := abs_add_le (e v i - s * e w i) (s * e w i)
  rw [sub_add_cancel, abs_mul] at h
  have hsmul := mul_le_mul_of_nonneg_right hs1 (abs_nonneg (e w i))
  linarith

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
