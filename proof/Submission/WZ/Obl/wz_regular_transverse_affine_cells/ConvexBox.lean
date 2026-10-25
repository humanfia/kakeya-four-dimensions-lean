-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.ConvexBox.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.OrthogonalBox
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabSelection

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set
open scoped ENNReal

lemma frameLinear_norm_le (b : Basis (Fin 3) ℝ E) {R : ℝ}
    (hb : ∀ i, ‖b i‖ ≤ R) (q : E) : ‖frameLinear b q‖ ≤ 3 * R * ‖q‖ := by
  rw [frameLinear_apply]
  calc ‖∑ i, q i • b i‖ ≤ ∑ i, ‖q i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖q‖ * R := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (WangZahlLot.Obl.wz_balanced_cluster_cover.abs_apply_le_norm q i)
        (hb i) (norm_nonneg _) (norm_nonneg q)
    _ = _ := by simp; ring

/-- Every bounded convex body with interior admits an orthogonal outer box of
comparable volume. The widths are ordered, bounded below by its interior radius,
and bounded above by its containing-ball radius. -/
lemma exists_comparable_orthogonal_box {U : Set E} (hUc : IsCompact U) (hU : Convex ℝ U)
    {x : E} {r R : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ U)
    (hbound : U ⊆ Metric.closedBall (0 : E) R) :
    ∃ (u : OrthonormalBasis (Fin 3) ℝ E) (w : Fin 3 → ℝ),
      (∀ i, 0 < w i) ∧ Antitone w ∧ (∀ i, r / 2 ≤ w i ∧ w i ≤ 12 * R) ∧
      U ⊆ orthogonalBox w x u ∧
      ENNReal.ofReal (1 / 4096 : ℝ) * volume (orthogonalBox w x u) ≤ volume U := by
  obtain ⟨b, hb, hcoord⟩ := exists_bounded_frame_of_ball hUc hr hball
  have hx : x ∈ U := hball (Metric.mem_ball_self hr)
  have hxR : ‖x‖ ≤ R := by simpa using hbound hx
  have hbR : ∀ i, ‖b i‖ ≤ 2 * R := by
    intro i
    have hiR : ‖x + b i‖ ≤ R := by simpa using hbound (hb i)
    calc ‖b i‖ = ‖(x + b i) - x‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖x + b i‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  obtain ⟨u, d, hd, hdanti, hdcoord, hdprod, hdattain⟩ := exists_principal_axes (frameLinear b)
  let w : Fin 3 → ℝ := fun i => 2 * d i
  have hwpos : ∀ i, 0 < w i := fun i => mul_pos (by norm_num) (hd i)
  have hcover : U ⊆ orthogonalBox w x u := by
    exact (subset_frameAffine_ball x b hcoord).trans
      (image_ball_subset_orthogonalBox (frameLinear b) x u d (fun i => (hd i).le) hdcoord 2)
  have houter : volume (orthogonalBox w x u) =
      ENNReal.ofReal (64 * |LinearMap.det (frameLinear b : E →ₗ[ℝ] E)|) := by
    rw [volume_orthogonalBox w (fun i => (hwpos i).le)]
    unfold w
    rw [Finset.prod_mul_distrib, hdprod]
    norm_num
    ring
  have hinner : ENNReal.ofReal |LinearMap.det (frameLinear b : E →ₗ[ℝ] E)| *
      ENNReal.ofReal (1 / 64 : ℝ) ≤ volume U := by
    rw [← volume_quarter_cube, ← frameAffine_volume]
    exact measure_mono (frameAffine_inner_cube_subset hU x hx b hb)
  refine ⟨u, w, hwpos, ?_, ?_, hcover, ?_⟩
  · intro i j hij
    exact mul_le_mul_of_nonneg_left (hdanti hij) (by norm_num)
  · intro i
    constructor
    · apply half_radius_le_slab_width (u.norm_eq_one i) hr
      intro q hq
      have h := hcover (hball hq) i
      simpa only [slab, mem_ofPred_eq, innerSL_apply_apply, inner_sub_right] using h
    · obtain ⟨q, hq, hqi⟩ := hdattain i
      have hnorm := frameLinear_norm_le b hbR q
      rw [hq] at hnorm
      have hinner := abs_real_inner_le_norm (u i) (frameLinear b q)
      rw [hqi, u.norm_eq_one, one_mul, abs_of_pos (hd i)] at hinner
      dsimp [w]
      nlinarith
  · calc ENNReal.ofReal (1 / 4096 : ℝ) * volume (orthogonalBox w x u)
        = ENNReal.ofReal |LinearMap.det (frameLinear b : E →ₗ[ℝ] E)| *
          ENNReal.ofReal (1 / 64 : ℝ) := by
            rw [houter, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (abs_nonneg _)]
            congr 1
            ring
      _ ≤ volume U := hinner

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
