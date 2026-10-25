-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StripRadialGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadialTransverse
import Submission.WZ.Obl.wz_separated_projection_dichotomy.IndexedGeometry

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem area_perp_right (x y : Plane) : area x (perp y) = -inner ℝ x y := by
  simp [area_coordinates, plane_inner, perp]
  ring

theorem radial_strip_angle {b y n : Plane} {s : ℝ} (hby : b ≠ y)
    (hy : s ≤ |inner ℝ y n - inner ℝ b n|) (hfar : ‖b - y‖ ≤ 16) :
    s / 16 ≤ |area n (perp (radialDirection b y))| := by
  have hscale : |inner ℝ y n - inner ℝ b n| =
      ‖b - y‖ * |inner ℝ (radialDirection b y) n| := by
    rw [← inner_sub_left, show y - b = -(b - y) by abel, inner_neg_left,
      abs_neg, ← radialDirection_scale hby, real_inner_smul_left, abs_mul,
      abs_of_nonneg (norm_nonneg _)]
    rw [radialDirection_scale hby]
  rw [hscale] at hy
  rw [area_perp_right, abs_neg, real_inner_comm (radialDirection b y) n]
  nlinarith [mul_le_mul_of_nonneg_right hfar (abs_nonneg (inner ℝ (radialDirection b y) n))]

/-- Within a strip, radial directions from a point away from its center line
control distance, up to the strip width. -/
theorem strip_radial_diameter {b x y n : Plane} {c w s r : ℝ}
    (hn : ‖n‖ = 1) (hs : 0 < s) (hr : 0 ≤ r)
    (hbx : b ≠ x) (hby : b ≠ y)
    (hx : |inner ℝ x n - c| ≤ w) (hy : |inner ℝ y n - c| ≤ w)
    (hgap : s ≤ |inner ℝ y n - inner ℝ b n|)
    (hfarx : ‖b - x‖ ≤ 16) (hfary : ‖b - y‖ ≤ 16)
    (hdir : dist (radialDirection b x) (radialDirection b y) ≤ 2 * r) :
    dist x y ≤ (32 * w + 1024 * r) / s := by
  let u := radialDirection b y
  have hu : ‖u‖ = 1 := radialDirection_norm hby
  have hxu : |inner ℝ x (perp u) - inner ℝ b (perp u)| ≤ 32 * r := by
    rw [← inner_sub_left]
    calc |inner ℝ (x - b) (perp u)| ≤ ‖b - x‖ * dist (radialDirection b x) u :=
          abs_inner_perp_le_radial_distance hbx hu
      _ ≤ 16 * (2 * r) := mul_le_mul hfarx hdir dist_nonneg (by norm_num)
      _ = _ := by ring
  have hyu : |inner ℝ y (perp u) - inner ℝ b (perp u)| ≤ 32 * r := by
    have hz := abs_inner_perp_le_radial_distance hby hu
    change |inner ℝ (y - b) (perp u)| ≤ ‖b - y‖ * dist u u at hz
    rw [dist_self, mul_zero] at hz
    rw [← inner_sub_left]
    exact hz.trans (by positivity)
  have hdiam := transverse_strips_diameter hn ((perp_norm u).trans hu)
    (by positivity : 0 < s / 16) (radial_strip_angle hby hgap hfary) hx hy hxu hyu
  convert hdiam using 1 <;> field_simp <;> ring

/-- If the strip is no wider than the angular cap scale, one cap has a
small spatial preimage. -/
theorem strip_radial_cap_diameter {b x y n z : Plane} {c w s r : ℝ}
    (hn : ‖n‖ = 1) (hs : 0 < s) (hr : 0 ≤ r) (hwr : w ≤ r)
    (hbx : b ≠ x) (hby : b ≠ y)
    (hx : |inner ℝ x n - c| ≤ w) (hy : |inner ℝ y n - c| ≤ w)
    (hgap : s ≤ |inner ℝ y n - inner ℝ b n|)
    (hfarx : ‖b - x‖ ≤ 16) (hfary : ‖b - y‖ ≤ 16)
    (hxz : dist (radialDirection b x) z ≤ r) (hyz : dist (radialDirection b y) z ≤ r) :
    dist x y ≤ 2048 * r / s := by
  have hdir : dist (radialDirection b x) (radialDirection b y) ≤ 2 * r :=
    (dist_triangle_right _ _ z).trans (by linarith)
  exact (strip_radial_diameter hn hs hr hbx hby hx hy hgap hfarx hfary hdir).trans
    (div_le_div_of_nonneg_right (by linarith) hs.le)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
