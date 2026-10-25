-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TransverseStrips.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CircleGeometry
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Strips

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- Signed planar area, in the convention fixed by `perp`. -/
noncomputable def area (x y : Plane) : ℝ := inner ℝ x (perp y)

theorem area_coordinates (x y : Plane) : area x y = x 1 * y 0 - x 0 * y 1 := by
  simp [area, plane_inner, perp]
  ring

theorem area_antisymm (x y : Plane) : area x y = -area y x := by
  simp only [area_coordinates]
  ring

theorem area_self (x : Plane) : area x x = 0 := by
  rw [area_coordinates]
  ring

theorem area_sub_left (x y z : Plane) : area (x - y) z = area x z - area y z :=
  inner_sub_left _ _ _

theorem area_sub_right (x y z : Plane) : area x (y - z) = area x y - area x z := by
  simp [area_coordinates]
  ring

theorem area_smul_left (t : ℝ) (x y : Plane) : area (t • x) y = t * area x y :=
  real_inner_smul_left _ _ _

theorem area_smul_right (t : ℝ) (x y : Plane) : area x (t • y) = t * area x y := by
  simp [area_coordinates]
  ring

theorem abs_area_le_norm (x y : Plane) : |area x y| ≤ ‖x‖ * ‖y‖ := by
  simpa only [area, perp_norm] using abs_real_inner_le_norm x (perp y)

theorem area_lipschitz_unit {x y u v : Plane} (hy : ‖y‖ = 1) (hu : ‖u‖ = 1) :
    |area x y - area u v| ≤ dist x u + dist y v := by
  have hid : area x y - area u v = area (x - u) y + area u (y - v) := by
    rw [area_sub_left, area_sub_right]
    ring
  rw [hid]
  calc |area (x - u) y + area u (y - v)| ≤ |area (x - u) y| + |area u (y - v)| := abs_add_le _ _
    _ ≤ ‖x - u‖ * ‖y‖ + ‖u‖ * ‖y - v‖ :=
      add_le_add (abs_area_le_norm _ _) (abs_area_le_norm _ _)
    _ = _ := by rw [hy, hu, mul_one, one_mul, dist_eq_norm, dist_eq_norm]

theorem area_smul_identity (u v w : Plane) :
    area u v • w = inner ℝ w u • perp v - inner ℝ w v • perp u := by
  ext i
  fin_cases i <;> simp [area_coordinates, plane_inner, perp] <;> ring

/-- Two scalar projections control a vector when their normals are transverse. -/
theorem area_mul_norm_le (u v w : Plane) :
    |area u v| * ‖w‖ ≤ |inner ℝ w u| * ‖v‖ + |inner ℝ w v| * ‖u‖ := by
  calc |area u v| * ‖w‖ = ‖area u v • w‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ = ‖inner ℝ w u • perp v - inner ℝ w v • perp u‖ := by rw [area_smul_identity]
    _ ≤ ‖inner ℝ w u • perp v‖ + ‖inner ℝ w v • perp u‖ := norm_sub_le _ _
    _ = _ := by simp only [norm_smul, Real.norm_eq_abs, perp_norm]

theorem transverse_strips_diameter {u v x y : Plane} {a b r s t : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ht : 0 < t) (hangle : t ≤ |area u v|)
    (hxu : |inner ℝ x u - a| ≤ r) (hyu : |inner ℝ y u - a| ≤ r)
    (hxv : |inner ℝ x v - b| ≤ s) (hyv : |inner ℝ y v - b| ≤ s) :
    dist x y ≤ (2 * r + 2 * s) / t := by
  have hwu : |inner ℝ (x - y) u| ≤ 2 * r := by
    rw [inner_sub_left, show inner ℝ x u - inner ℝ y u =
      (inner ℝ x u - a) - (inner ℝ y u - a) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have hwv : |inner ℝ (x - y) v| ≤ 2 * s := by
    rw [inner_sub_left, show inner ℝ x v - inner ℝ y v =
      (inner ℝ x v - b) - (inner ℝ y v - b) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have hnorm := area_mul_norm_le u v (x - y)
  rw [hu, hv, mul_one, mul_one] at hnorm
  apply (le_div_iff₀ ht).mpr
  rw [dist_eq_norm]
  calc ‖x - y‖ * t ≤ |area u v| * ‖x - y‖ := by nlinarith [norm_nonneg (x - y)]
    _ ≤ _ := hnorm.trans (by linarith)

/-- An intersection of transverse strips is contained in a quantitatively
controlled ball about any of its points. -/
theorem transverse_strips_subset_ball {u v y : Plane} {a b r s t : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ht : 0 < t) (hangle : t ≤ |area u v|)
    (hyu : y ∈ Strip u a r) (hyv : y ∈ Strip v b s) :
    Strip u a r ∩ Strip v b s ⊆ Metric.closedBall y ((2 * r + 2 * s) / t) := by
  intro x hx
  exact transverse_strips_diameter hu hv ht hangle hx.1.le hyu.le hx.2.le hyv.le

end WangZahlLot.Obl.wz_separated_projection_dichotomy
