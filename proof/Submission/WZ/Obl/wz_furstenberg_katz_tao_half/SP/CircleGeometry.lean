-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.CircleGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.Basic

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

open Set Metric

noncomputable def perp (v : Plane) : Plane := WithLp.toLp 2 ![-v 1, v 0]

theorem plane_inner (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem perp_norm (v : Plane) : ‖perp v‖ = ‖v‖ := by
  have hs : ‖perp v‖ ^ 2 = ‖v‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, perp, add_comm]
  nlinarith [norm_nonneg (perp v), norm_nonneg v]

theorem perp_inner (v : Plane) : inner ℝ v (perp v) = 0 := by
  rw [plane_inner]
  simp [perp]
  ring

theorem inner_sq_add_perp_inner_sq (x v : Plane) :
    (inner ℝ x v) ^ 2 + (inner ℝ x (perp v)) ^ 2 = ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
  simp only [plane_inner, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [perp]
  ring

theorem unit_close_of_inner_decomposition {x w : Plane} {t : ℝ}
    (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hdecomp : t ^ 2 + (inner ℝ x w) ^ 2 = 1) (hs : 0 ≤ inner ℝ x w) :
    dist x w ≤ 2 * |t| := by
  have hs1 : inner ℝ x w ≤ 1 := by simpa [hx, hw] using real_inner_le_norm x w
  have hs2 : (inner ℝ x w) ^ 2 ≤ inner ℝ x w := by
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]
  apply (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ 2 * |t|)).mp
  rw [dist_eq_norm, norm_sub_sq_real, hx, hw]
  nlinarith [sq_nonneg t, sq_abs t]

/-- A thin strip through the origin cuts the unit circle into two small
arcs, each lying in a ball about a perpendicular unit vector. -/
theorem unit_circle_near_perpendicular {x e : Plane} (hx : ‖x‖ = 1) (he : ‖e‖ = 1) :
    dist x (perp e) ≤ 2 * |inner ℝ x e| ∨
      dist x (-perp e) ≤ 2 * |inner ℝ x e| := by
  have hp : ‖perp e‖ = 1 := (perp_norm e).trans he
  have hid : (inner ℝ x e) ^ 2 + (inner ℝ x (perp e)) ^ 2 = 1 := by
    simpa [hx, he] using inner_sq_add_perp_inner_sq x e
  by_cases hs : 0 ≤ inner ℝ x (perp e)
  · exact Or.inl (unit_close_of_inner_decomposition hx hp hid hs)
  · right
    apply unit_close_of_inner_decomposition hx (by simpa using hp)
    · simpa only [inner_neg_right, neg_sq] using hid
    · simpa only [inner_neg_right] using neg_nonneg.mpr (le_of_not_ge hs)

/-- The same arc bound for a non-normalized nonzero normal vector. -/
theorem unit_circle_strip_two_balls {v : Plane} (hv : v ≠ 0) {s : ℝ} :
    ∃ e : Plane, ‖e‖ = 1 ∧
      ∀ x : Plane, ‖x‖ = 1 → |inner ℝ x v| ≤ s →
        dist x e ≤ 2 * s / ‖v‖ ∨ dist x (-e) ≤ 2 * s / ‖v‖ := by
  let u : Plane := ‖v‖⁻¹ • v
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvp.le), hvp.ne']
  refine ⟨perp u, (perp_norm u).trans hu, ?_⟩
  intro x hx hs
  have hi : |inner ℝ x u| = |inner ℝ x v| / ‖v‖ := by
    simp only [u, real_inner_smul_right, abs_mul, abs_inv, abs_of_pos hvp, div_eq_mul_inv]
    ring
  have hbound : 2 * |inner ℝ x u| ≤ 2 * s / ‖v‖ := by
    rw [hi, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hvp.le
  exact (unit_circle_near_perpendicular hx hu).imp (fun h => h.trans hbound) (fun h => h.trans hbound)

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
