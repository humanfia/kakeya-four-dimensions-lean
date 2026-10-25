-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.RadialTransverse.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TransverseStrips
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadialGeometry

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem area_perp (u v : Plane) : area (perp u) (perp v) = area u v := by
  simp [area_coordinates, perp]
  ring

theorem radial_area_identity {b b' x : Plane} (hbx : b ≠ x) (hb'x : b' ≠ x) :
    |area (x - b) (b' - b)| =
      ‖b - x‖ * ‖b' - x‖ * |area (radialDirection b x) (radialDirection b' x)| := by
  have hid : area (b - x) (b' - x) = -area (x - b) (b' - b) := by
    simp only [area_coordinates, PiLp.sub_apply]
    ring
  calc |area (x - b) (b' - b)| = |area (b - x) (b' - x)| := by rw [hid, abs_neg]
    _ = |area (‖b - x‖ • radialDirection b x) (‖b' - x‖ • radialDirection b' x)| := by
      rw [radialDirection_scale hbx, radialDirection_scale hb'x]
    _ = _ := by
      rw [area_smul_left, area_smul_right, abs_mul, abs_mul,
        abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
      ring

theorem radial_area_lower {b b' x : Plane} {q s : ℝ}
    (hbx : b ≠ x) (hb'x : b' ≠ x) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hsep : q ≤ ‖b' - b‖) (hfar : ‖b - x‖ ≤ 8) (hfar' : ‖b' - x‖ ≤ 8)
    (hline : s * ‖b' - b‖ ≤ |area (x - b) (b' - b)|) :
    q * s / 64 ≤ |area (radialDirection b x) (radialDirection b' x)| := by
  have hprod : ‖b - x‖ * ‖b' - x‖ ≤ 64 :=
    (mul_le_mul hfar hfar' (norm_nonneg _) (by norm_num)).trans (by norm_num)
  rw [radial_area_identity hbx hb'x] at hline
  have hscaled := mul_le_mul_of_nonneg_right hprod
    (abs_nonneg (area (radialDirection b x) (radialDirection b' x)))
  have hqs := mul_le_mul_of_nonneg_left hsep hs
  linarith

/-- Away from the line joining two pins, cap centers through the same point
have quantitatively transverse directions. -/
theorem radial_cap_transverse {b b' x u v : Plane} {q s r : ℝ}
    (hbx : b ≠ x) (hb'x : b' ≠ x) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hq : 0 ≤ q) (hs : 0 ≤ s) (hr : r ≤ q * s / 256)
    (hsep : q ≤ ‖b' - b‖) (hfar : ‖b - x‖ ≤ 8) (hfar' : ‖b' - x‖ ≤ 8)
    (hline : s * ‖b' - b‖ ≤ |area (x - b) (b' - b)|)
    (hxu : dist (radialDirection b x) u ≤ r) (hxv : dist (radialDirection b' x) v ≤ r) :
    q * s / 128 ≤ |area u v| := by
  have hrad := radial_area_lower hbx hb'x hq hs hsep hfar hfar' hline
  have hlip := area_lipschitz_unit (x := radialDirection b x) (u := u)
    (v := v) (radialDirection_norm hb'x) hu
  have habs : |area (radialDirection b x) (radialDirection b' x)| ≤
      |area (radialDirection b x) (radialDirection b' x) - area u v| + |area u v| := by
    simpa only [sub_add_cancel] using abs_add_le
      (area (radialDirection b x) (radialDirection b' x) - area u v) (area u v)
  linarith

theorem radial_cap_inner_bound {b x u : Plane} {r : ℝ}
    (hbx : b ≠ x) (hu : ‖u‖ = 1) (hr : 0 ≤ r) (hfar : ‖b - x‖ ≤ 8)
    (hcap : dist (radialDirection b x) u ≤ r) :
    |inner ℝ x (perp u) - inner ℝ b (perp u)| ≤ 8 * r := by
  rw [← inner_sub_left]
  calc |inner ℝ (x - b) (perp u)| ≤ ‖b - x‖ * dist (radialDirection b x) u :=
      abs_inner_perp_le_radial_distance hbx hu
    _ ≤ 8 * r := mul_le_mul hfar hcap dist_nonneg (by norm_num)

/-- Two radial caps with transverse central directions have a small spatial
intersection. This retains all multiplicities of the original finite set. -/
theorem radial_cap_diameter {b b' x y u v : Plane} {r t : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hr : 0 ≤ r) (ht : 0 < t)
    (hangle : t ≤ |area u v|)
    (hx : b ≠ x ∧ b' ≠ x ∧ ‖b - x‖ ≤ 8 ∧ ‖b' - x‖ ≤ 8)
    (hy : b ≠ y ∧ b' ≠ y ∧ ‖b - y‖ ≤ 8 ∧ ‖b' - y‖ ≤ 8)
    (hxu : dist (radialDirection b x) u ≤ r) (hxv : dist (radialDirection b' x) v ≤ r)
    (hyu : dist (radialDirection b y) u ≤ r) (hyv : dist (radialDirection b' y) v ≤ r) :
    dist x y ≤ 32 * r / t := by
  have h := transverse_strips_diameter ((perp_norm u).trans hu) ((perp_norm v).trans hv)
    ht (by simpa only [area_perp] using hangle)
    (radial_cap_inner_bound hx.1 hu hr hx.2.2.1 hxu)
    (radial_cap_inner_bound hy.1 hu hr hy.2.2.1 hyu)
    (radial_cap_inner_bound hx.2.1 hv hr hx.2.2.2 hxv)
    (radial_cap_inner_bound hy.2.1 hv hr hy.2.2.2 hyv)
  convert h using 1 <;> ring

end WangZahlLot.Obl.wz_separated_projection_dichotomy
