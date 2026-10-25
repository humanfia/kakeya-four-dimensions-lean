-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.SlopeFrame.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.AxialGeometry
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Geometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover

/-! Frames following a selected transverse slope. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory

/-- There is a frame along `u` whose narrow coordinate follows its first slope
in the old frame. -/
theorem frame_of_coordinate_slope (e : V ≃ₗᵢ[ℝ] V) {u : V}
    (hu : ‖u‖ = 1) (hu2 : e u 2 ≠ 0) :
    ∃ g : V ≃ₗᵢ[ℝ] V, (∀ p, g p 2 = inner ℝ u p) ∧
      ∀ p, |g p 0| ≤ 2 * |e p 0 - (e u 0 / e u 2) * e p 2| := by
  let t : ℝ := e u 0 / e u 2
  let n : V := e.symm (EuclideanSpace.single 0 1 - t • EuclideanSpace.single 2 1)
  have hn0 : e n 0 = 1 := by simp [n]
  have hnorm : 1 ≤ ‖n‖ := by
    have hh := wz_move_two_long_grains_gain.abs_coord_le_norm (e n) 0
    simpa only [hn0, abs_one, e.norm_map] using hh
  have hnpos : 0 < ‖n‖ := by linarith
  have hinner (p : V) : inner ℝ n p = e p 0 - t * e p 2 := by
    rw [← e.inner_map_map n p]
    simp [n, inner_sub_left, inner_smul_left, EuclideanSpace.inner_single_left]
  have hnu : inner ℝ n u = 0 := by rw [hinner]; dsimp [t]; field_simp; ring
  let N : V := ‖n‖⁻¹ • n
  have hN : ‖N‖ = 1 := by
    rw [show N = ‖n‖⁻¹ • n by rfl, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnpos)]
    exact inv_mul_cancel₀ hnpos.ne'
  have hNu : inner ℝ N u = 0 := by dsimp [N]; rw [inner_smul_left, hnu, mul_zero]
  obtain ⟨g, hg2, hg0⟩ := wz_flat_cluster_slab_filling.adapted_frame hN hu
    (by rw [hNu, abs_zero]; norm_num)
  refine ⟨g, hg2, fun p => ?_⟩
  have hninv : ‖n‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnorm
  calc
    |g p 0| ≤ 2 * |inner ℝ N p| := by simpa only [hNu, abs_zero, zero_mul, add_zero] using hg0 p
    _ = 2 * (‖n‖⁻¹ * |e p 0 - t * e p 2|) := by
      dsimp [N]
      rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.mpr hnpos), hinner]
    _ ≤ 2 * |e p 0 - t * e p 2| := by nlinarith [abs_nonneg (e p 0 - t * e p 2)]

/-- In a frame along `u`, transverse coordinates are bounded by the difference
of the two old slopes. -/
theorem frame_transverse_slope_bound (e g : V ≃ₗᵢ[ℝ] V) {u : V}
    (hu : ‖u‖ = 1) (hu2 : e u 2 ≠ 0) (hg2 : ∀ p, g p 2 = inner ℝ u p)
    (p : V) :
    |g p 1| ≤ |e p 0 - (e u 0 / e u 2) * e p 2| +
      |e p 1 - (e u 1 / e u 2) * e p 2| := by
  have hgu := wz_flat_cluster_slab_filling.frame_v hu hg2
  let r : V := p - (e p 2 / e u 2) • u
  have hr (j : Fin 3) : e r j = e p j - (e p 2 / e u 2) * e u j := by
    dsimp [r]
    rw [map_sub, map_smul]
    rfl
  have hr2 : e r 2 = 0 := by rw [hr]; field_simp; ring
  have hg : g r 1 = g p 1 := by
    dsimp [r]
    rw [map_sub, map_smul]
    change g p 1 - (e p 2 / e u 2) * g u 1 = g p 1
    rw [hgu.2.1, mul_zero, sub_zero]
  calc
    _ = |g r 1| := congrArg abs hg.symm
    _ ≤ ‖r‖ := by simpa only [g.norm_map] using wz_move_two_long_grains_gain.abs_coord_le_norm (g r) 1
    _ = ‖e r‖ := (e.norm_map r).symm
    _ ≤ |e r 0| + |e r 1| + |e r 2| := wz_clustered_cover_volume_gain.norm_le_coord_sum _
    _ = _ := by rw [hr2, abs_zero, add_zero, hr, hr]; congr 2 <;> ring

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
