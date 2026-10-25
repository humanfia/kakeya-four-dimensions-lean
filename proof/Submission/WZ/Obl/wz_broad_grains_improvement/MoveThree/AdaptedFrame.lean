-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AdaptedFrame.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AdaptedFrame.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, AdaptedFrame.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.FlatGeometry

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis inner_boxAxis)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (norm_sq_coords inner_coords)

/-- The frame bound used by slab filling also controls its middle axis in the
slab normal direction. -/
theorem adapted_middle_normal {u v : V} (hu : ‖u‖ = 1) (g : V ≃ₗᵢ[ℝ] V)
    (hg : ∀ w, |g w 0| ≤ 2 * (|inner ℝ u w| + |inner ℝ u v| * ‖w‖)) :
    |inner ℝ u (boxAxis g 1)| ≤ 2 * |inner ℝ u v| := by
  let w : V := g.symm (WithLp.toLp 2 ![g u 1, -(g u 0), 0])
  have hw : g w = WithLp.toLp 2 ![g u 1, -(g u 0), 0] := g.apply_symm_apply _
  have horth : inner ℝ u w = 0 := by
    rw [← g.inner_map_map, inner_coords, hw]
    simp only [WithLp.toLp_ofLp, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons]
    ring
  have hnorm : ‖w‖ ≤ 1 := by
    have h₁ := norm_sq_coords (g w)
    have h₂ := norm_sq_coords (g u)
    rw [g.norm_map, hw] at h₁
    rw [g.norm_map, hu] at h₂
    norm_num only [WithLp.toLp_ofLp, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, neg_sq, zero_pow, add_zero] at h₁
    nlinarith [norm_nonneg w, sq_nonneg (g u 2)]
  have hh := hg w
  rw [horth, abs_zero, zero_add, hw] at hh
  have he : inner ℝ u (boxAxis g 1) = g u 1 := by rw [real_inner_comm, inner_boxAxis]
  rw [he]
  change |g u 1| ≤ 2 * (|inner ℝ u v| * ‖w‖) at hh
  exact hh.trans (by nlinarith [abs_nonneg (inner ℝ u v)])

/-- The last axis of an adapted coordinate frame is the stem direction. -/
theorem adapted_long_axis {v : V} (hv : ‖v‖ = 1) (g : V ≃ₗᵢ[ℝ] V)
    (hg : ∀ p, g p 2 = inner ℝ v p) : boxAxis g 2 = v := by
  obtain ⟨h₀, h₁, h₂⟩ := WangZahlLot.Obl.wz_flat_cluster_slab_filling.frame_v hv hg
  apply g.injective
  simp only [boxAxis, g.apply_symm_apply]
  ext i
  fin_cases i <;> simp_all [EuclideanSpace.basisFun_apply]

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
