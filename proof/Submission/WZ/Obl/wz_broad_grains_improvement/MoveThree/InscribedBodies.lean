-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.InscribedBodies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/InscribedBodies.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_nsp_convex_test_family
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TSGeometry

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric

noncomputable section

/-- A convex body with a macroscopic diameter and an interior ball contains
a tube of fixed length. This uses the accepted midpoint-ball inclusion. -/
theorem convex_body_inscribed_tube {r : ℝ} (hr : 0 < r) {W : Set V} {z : V}
    (hconv : Convex ℝ W) (hball : ball z r ⊆ W)
    (hlong : ∃ p ∈ W, ∃ q ∈ W, (1 / 4 : ℝ) ≤ dist p q) :
    ∃ v : V, ‖v‖ = 1 ∧ T (r / 2) z ((1 / 16 : ℝ) • v) ⊆ W := by
  have hz : z ∈ W := hball (mem_ball_self hr)
  obtain ⟨p, hp, q, hq, hpq⟩ := hlong
  have hfar : ∃ w ∈ W, (1 / 8 : ℝ) ≤ ‖w - z‖ := by
    by_cases hh : (1 / 8 : ℝ) ≤ ‖p - z‖
    · exact ⟨p, hp, hh⟩
    · refine ⟨q, hq, ?_⟩
      have ht := dist_triangle p z q
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev z q] at ht
      rw [dist_eq_norm] at hpq
      linarith
  obtain ⟨w, hw, hd⟩ := hfar
  let d := ‖w - z‖
  have hdpos : 0 < d := by dsimp [d]; linarith
  let v := d⁻¹ • (w - z)
  have hv : ‖v‖ = 1 := by
    rw [show v = d⁻¹ • (w - z) from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hdpos)]
    exact inv_mul_cancel₀ hdpos.ne'
  refine ⟨v, hv, ?_⟩
  intro x hx
  obtain ⟨t, ht, hxt⟩ := WangZahlLot.Obl.wz_extremal_lipschitz_grains.exists_param_of_mem_Tube hx
  let s := t / (8 * d)
  have hs : 0 ≤ s := div_nonneg ht.1 (by positivity)
  have hs1 : s ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 8 * d)).mpr
    dsimp [d]
    linarith [ht.2]
  let u := z + s • (w - z)
  have hu : u ∈ W := by
    convert hconv hz hw (sub_nonneg.mpr hs1) hs (by ring : 1 - s + s = 1) using 1
    dsimp [u]
    module
  have he : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • z = z + t • ((1 / 16 : ℝ) • v) := by
    have hs' : (1 / 2 : ℝ) * s = t * (1 / 16 : ℝ) * d⁻¹ := by
      dsimp [s]
      field_simp
      ring
    dsimp [u, v]
    simp only [smul_add, smul_sub, smul_smul]
    rw [hs']
    module
  apply WangZahlLot.Obl.wz_nsp_convex_test_family.ball_midpoint_subset hconv hball hu
  rw [mem_ball, dist_eq_norm, he]
  exact hxt

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
