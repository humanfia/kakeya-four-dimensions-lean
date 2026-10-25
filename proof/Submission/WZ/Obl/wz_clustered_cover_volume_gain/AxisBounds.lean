-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.AxisBounds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseNormals
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainAxes

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open WangZahlLot.Obl.wz_flat_factored_improvement (Space diagonalMap_apply)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd pd_triangle)

lemma coord_abs_le_of_projective (u v : Space) (j : Fin 3) :
    |u j| ≤ |v j| + pd u v := by
  have hh := abs_inner_le_projective u v (EuclideanSpace.basisFun (Fin 3) ℝ j)
  have hu : inner ℝ u (EuclideanSpace.basisFun (Fin 3) ℝ j) = u j := by
    rw [real_inner_comm, EuclideanSpace.basisFun_inner]
  have hv : inner ℝ v (EuclideanSpace.basisFun (Fin 3) ℝ j) = v j := by
    rw [real_inner_comm, EuclideanSpace.basisFun_inner]
  simpa only [hu, hv, (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one, mul_one, pd] using hh

lemma coarse_norm_of_coords {θ C : ℝ} (hθ : 0 < θ) {p : Space} (hp : ‖p‖ = 1)
    (hp0 : |p 0| ≤ C * θ) (hp1 : |p 1| ≤ C * θ) :
    ‖coarseLinear θ p‖ ≤ 2 * C + 1 := by
  have hp2 : |p 2| ≤ 1 := by simpa [hp, Real.norm_eq_abs] using PiLp.norm_apply_le p 2
  have hh := norm_le_coord_sum (coarseLinear θ p)
  norm_num [coarseLinear, diagonalMap_apply, abs_mul, abs_of_pos hθ, abs_of_pos (inv_pos.mpr hθ)] at hh
  change ‖coarseLinear θ p‖ ≤ θ⁻¹ * |p 0| + θ⁻¹ * |p 1| + |p 2| at hh
  have h0 : θ⁻¹ * |p 0| ≤ C := (inv_mul_le_iff₀ hθ).mpr (by simpa [mul_comm] using hp0)
  have h1 : θ⁻¹ * |p 1| ≤ C := (inv_mul_le_iff₀ hθ).mpr (by simpa [mul_comm] using hp1)
  linarith

/-- Uniform geometric constants for grains lying in one coarse tube frame. -/
lemma coarse_grain_axis_bounds {θ ρ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρθ : ρ ≤ θ)
    {n l w : Space} (hn : ‖n‖ = 1) (hl : ‖l‖ = 1) (hw : ‖w‖ = 1)
    (hnl : inner ℝ n l = 0) (halign : pd l w ≤ 20 * ρ)
    (hw0 : |w 0| ≤ θ) (hw1 : |w 1| ≤ θ) :
    ‖coarseLinear θ l‖ ≤ 43 ∧ ‖dualLinear θ n‖ ≤ 25 * θ := by
  have hl0 : |l 0| ≤ 21 * θ := (coord_abs_le_of_projective l w 0).trans (by linarith)
  have hl1 : |l 1| ≤ 21 * θ := (coord_abs_le_of_projective l w 1).trans (by linarith)
  have hnorm := coarse_norm_of_coords hθ hl hl0 hl1
  have hcoarse := coordinate_axis_close hθ.le hw hw0 hw1
  have hangle : pd l (EuclideanSpace.basisFun (Fin 3) ℝ 2) ≤ 23 * θ :=
    (pd_triangle l w _).trans (by linarith)
  have hn2 := perpendicular_axis_coordinate hn hnl hangle
  have hnormal := dualLinear_normal_upper hθ (by norm_num : (0 : ℝ) ≤ 23) hn hn2
  constructor
  · norm_num at hnorm ⊢
    exact hnorm
  · norm_num at hnormal ⊢
    exact hnormal

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
