-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GrainAxes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxGeometry
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Geometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Metric
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd pd_nonneg pd_sq_le_areaSq areaSq_gram
  pd_triangle pd_isometry pd_symm norm_sq_coords)

/-- The frozen grain-axis condition gives quantitative projective alignment
with the parent tube direction. -/
lemma grain_axis_close {ρ : ℝ} (hρ : 0 ≤ ρ) (e : V ≃ₗᵢ[ℝ] V) {w : V}
    (hw : ‖w‖ = 1) (haxis : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2) :
    pd (boxAxis e 2) w ≤ 20 * ρ := by
  have hh := pd_sq_le_areaSq (boxAxis_norm e 2) hw
  rw [areaSq_gram, boxAxis_norm, hw, inner_boxAxis] at hh
  have hn := norm_sq_coords (e w)
  rw [e.norm_map, hw] at hn
  have hp := pd_nonneg (boxAxis e 2) w
  nlinarith

lemma tube_direction_box_bound {ρ a b c : ℝ} (hρ : 0 < ρ)
    (x w z : V) (e : V ≃ₗᵢ[ℝ] V) (hT : T ρ x w ⊆ P a b c z e) :
    |e w 0| ≤ a ∧ |e w 1| ≤ b ∧ |e w 2| ≤ c := by
  have hleft := hT (self_subset_thickening hρ _ (left_mem_segment ℝ x (x + w)))
  have hright := hT (self_subset_thickening hρ _ (right_mem_segment ℝ x (x + w)))
  have he (j : Fin 3) : e w j = e (x + w - z) j - e (x - z) j := by
    have heq : e w = e (x + w - z) - e (x - z) := by
      rw [← map_sub]
      congr 1
      abel
    exact congrArg (fun p : V => p j) heq
  refine ⟨?_, ?_, ?_⟩
  · rw [he 0]
    exact (abs_sub _ _).trans (by linarith [hleft.1, hright.1])
  · rw [he 1]
    exact (abs_sub _ _).trans (by linarith [hleft.2.1, hright.2.1])
  · rw [he 2]
    exact (abs_sub _ _).trans (by linarith [hleft.2.2, hright.2.2])

lemma coordinate_axis_close {θ : ℝ} (hθ : 0 ≤ θ) {w : V} (hw : ‖w‖ = 1)
    (hw0 : |w 0| ≤ θ) (hw1 : |w 1| ≤ θ) :
    pd w (EuclideanSpace.basisFun (Fin 3) ℝ 2) ≤ 3 * θ := by
  let e₂ := EuclideanSpace.basisFun (Fin 3) ℝ 2
  have he₂ : ‖e₂‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 2
  have hi : inner ℝ w e₂ = w 2 := by
    change inner ℝ w (EuclideanSpace.basisFun (Fin 3) ℝ 2) = w 2
    rw [real_inner_comm, EuclideanSpace.basisFun_inner]
  have hh := pd_sq_le_areaSq hw he₂
  rw [areaSq_gram, hw, he₂, hi] at hh
  have hn := norm_sq_coords w
  rw [hw] at hn
  have h0 : w 0 ^ 2 ≤ θ ^ 2 := by
    nlinarith [sq_abs (w 0), mul_nonneg (sub_nonneg.mpr hw0) (add_nonneg hθ (abs_nonneg (w 0)))]
  have h1 : w 1 ^ 2 ≤ θ ^ 2 := by
    nlinarith [sq_abs (w 1), mul_nonneg (sub_nonneg.mpr hw1) (add_nonneg hθ (abs_nonneg (w 1)))]
  change pd w e₂ ≤ 3 * θ
  have hp := pd_nonneg w e₂
  nlinarith

lemma perpendicular_axis_coordinate {n l : V} (hn : ‖n‖ = 1) (hnl : inner ℝ n l = 0)
    {s : ℝ} (hang : pd l (EuclideanSpace.basisFun (Fin 3) ℝ 2) ≤ s) : |n 2| ≤ s := by
  have hh := abs_inner_le_projective (EuclideanSpace.basisFun (Fin 3) ℝ 2) l n
  have hln : inner ℝ l n = 0 := by rw [real_inner_comm]; exact hnl
  rw [EuclideanSpace.basisFun_inner, hln, abs_zero, hn, mul_one, zero_add] at hh
  change |n 2| ≤ _ at hh
  apply hh.trans
  change pd (EuclideanSpace.basisFun (Fin 3) ℝ 2) l ≤ s
  rw [pd_symm]
  exact hang

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
