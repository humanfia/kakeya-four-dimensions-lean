-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StripProjectionGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Anisotropic

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem norm_le_frame_sum {e : Plane} (he : ‖e‖ = 1) (x : Plane) :
    ‖x‖ ≤ |inner ℝ x e| + |inner ℝ x (perp e)| := by
  calc ‖x‖ = ‖inner ℝ x e • e + inner ℝ x (perp e) • perp e‖ := by rw [unit_inner_decomposition he]
    _ ≤ ‖inner ℝ x e • e‖ + ‖inner ℝ x (perp e) • perp e‖ := norm_add_le _ _
    _ = _ := by simp only [norm_smul, Real.norm_eq_abs, perp_norm, he, mul_one]

theorem strip_difference_perp {e x y : Plane} {c t : ℝ}
    (hx : |inner ℝ x (perp e) - c| ≤ t) (hy : |inner ℝ y (perp e) - c| ≤ t) :
    |inner ℝ (x - y) (perp e)| ≤ 2 * t := by
  rw [inner_sub_left, show inner ℝ x (perp e) - inner ℝ y (perp e) =
    (inner ℝ x (perp e) - c) - (inner ℝ y (perp e) - c) by ring]
  exact (abs_sub _ _).trans (by linarith)

/-- A projection transverse to a strip controls spatial diameter above its
width. The explicit constants avoid separated-net choices. -/
theorem strip_dot_diameter {a e x y : Plane} {c t : ℝ}
    (he : ‖e‖ = 1) (ha : ‖a‖ ≤ 4) (ht : 0 ≤ t)
    (hA : 0 < |inner ℝ a e|)
    (hx : |inner ℝ x (perp e) - c| ≤ t) (hy : |inner ℝ y (perp e) - c| ≤ t)
    (hdot : |inner ℝ a (x - y)| ≤ 2 * t) :
    dist x y ≤ 18 * t / |inner ℝ a e| := by
  have hAe : |inner ℝ a e| ≤ 4 :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [he, mul_one] using ha)
  have hAn : |inner ℝ a (perp e)| ≤ 4 :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [perp_norm, he, mul_one] using ha)
  have hn := strip_difference_perp hx hy
  have hid : inner ℝ a e * inner ℝ (x - y) e =
      inner ℝ a (x - y) - inner ℝ a (perp e) * inner ℝ (x - y) (perp e) := by
    rw [inner_eq_frame_sum he a (x - y)]
    ring
  have hproj : |inner ℝ a e| * |inner ℝ (x - y) e| ≤ 10 * t := by
    rw [← abs_mul, hid]
    calc |inner ℝ a (x - y) - inner ℝ a (perp e) * inner ℝ (x - y) (perp e)| ≤
          |inner ℝ a (x - y)| + |inner ℝ a (perp e) * inner ℝ (x - y) (perp e)| := abs_sub _ _
      _ ≤ 2 * t + 4 * (2 * t) := by
        rw [abs_mul]
        exact add_le_add hdot (mul_le_mul hAn hn (abs_nonneg _) (by norm_num))
      _ = 10 * t := by ring
  have hnorm := mul_le_mul_of_nonneg_left (norm_le_frame_sum he (x - y)) hA.le
  have hperp := mul_le_mul hAe hn (abs_nonneg (inner ℝ (x - y) (perp e))) (by norm_num : (0 : ℝ) ≤ 4)
  apply (le_div_iff₀ hA).mpr
  rw [dist_eq_norm]
  nlinarith

theorem strip_dot_abs_bound {a e x b : Plane} {c t : ℝ}
    (he : ‖e‖ = 1) (ha : ‖a‖ ≤ 4) (ht : 0 ≤ t)
    (hxt : |inner ℝ x (perp e) - c| ≤ t) (hbt : |inner ℝ b (perp e) - c| ≤ t)
    (hxb : ‖x - b‖ ≤ 8) (htA : t ≤ |inner ℝ a e|) :
    |inner ℝ a (x - b)| ≤ 16 * |inner ℝ a e| := by
  have hn := strip_difference_perp hxt hbt
  have hAn : |inner ℝ a (perp e)| ≤ 4 :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [perp_norm, he, mul_one] using ha)
  have hde : |inner ℝ (x - b) e| ≤ 8 :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [he, mul_one] using hxb)
  rw [inner_eq_frame_sum he a (x - b)]
  calc |inner ℝ a e * inner ℝ (x - b) e + inner ℝ a (perp e) * inner ℝ (x - b) (perp e)| ≤
      |inner ℝ a e * inner ℝ (x - b) e| + |inner ℝ a (perp e) * inner ℝ (x - b) (perp e)| := abs_add_le _ _
    _ ≤ |inner ℝ a e| * 8 + 4 * (2 * t) := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hde (abs_nonneg _))
        (mul_le_mul hAn hn (abs_nonneg _) (by norm_num))
    _ ≤ _ := by linarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
