-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonconcentrated_dot_products.RadialGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.IndexedDirections

namespace WangZahlLot.Obl.wz_nonconcentrated_dot_products

open Set Metric

noncomputable def radialDirection (b x : Plane) : Plane := ‖b - x‖⁻¹ • (b - x)

theorem radialDirection_norm {b x : Plane} (hbx : b ≠ x) : ‖radialDirection b x‖ = 1 := by
  have hn : 0 < ‖b - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hbx)
  simp [radialDirection, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), hn.ne']

theorem radialDirection_scale {b x : Plane} (hbx : b ≠ x) :
    ‖b - x‖ • radialDirection b x = b - x := by
  have hn : ‖b - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hbx)
  simp [radialDirection, smul_smul, hn]

theorem radialDirection_dot {b x : Plane} (hbx : b ≠ x) (a : Plane) :
    inner ℝ a (b - x) = ‖b - x‖ * inner ℝ (radialDirection b x) a := by
  calc inner ℝ a (b - x) = inner ℝ a (‖b - x‖ • radialDirection b x) := by
        rw [radialDirection_scale hbx]
    _ = ‖b - x‖ * inner ℝ (radialDirection b x) a := by
        rw [real_inner_smul_right, real_inner_comm a (radialDirection b x)]

theorem abs_inner_perp_le_radial_distance {b x u : Plane} (hbx : b ≠ x) (hu : ‖u‖ = 1) :
    |inner ℝ (x - b) (perp u)| ≤ ‖b - x‖ * dist (radialDirection b x) u := by
  have hid : inner ℝ (radialDirection b x - u) (perp u) =
      inner ℝ (radialDirection b x) (perp u) := by rw [inner_sub_left, perp_inner, sub_zero]
  calc |inner ℝ (x - b) (perp u)| =
        ‖b - x‖ * |inner ℝ (radialDirection b x) (perp u)| := by
          rw [show x - b = -(b - x) by abel, inner_neg_left, abs_neg,
            ← radialDirection_scale hbx, real_inner_smul_left, abs_mul, abs_of_nonneg (norm_nonneg _)]
          rw [radialDirection_scale hbx]
    _ ≤ ‖b - x‖ * (‖radialDirection b x - u‖ * ‖perp u‖) := by
      rw [← hid]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by rw [perp_norm, hu, mul_one, dist_eq_norm]

end WangZahlLot.Obl.wz_nonconcentrated_dot_products
