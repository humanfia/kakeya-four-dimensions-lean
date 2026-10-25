-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AnisotropicStrips.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Anisotropic
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripRadialFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.MapFrostman

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem anisotropic_strip_bound {e x : Plane} {c w h : ℝ}
    (he : ‖e‖ = 1) (hh : 0 < h) (hx : |inner ℝ x (perp e) - c| ≤ w) :
    |inner ℝ (anisotropicMap e 1 h⁻¹ x) (perp e) - c / h| ≤ w / h := by
  rw [(anisotropicMap_inner he 1 h⁻¹ x).2,
    show h⁻¹ * inner ℝ x (perp e) - c / h = (inner ℝ x (perp e) - c) / h by ring,
    abs_div, abs_of_pos hh]
  exact div_le_div_of_nonneg_right hx hh.le

theorem anisotropic_strip_gap {e b x : Plane} {c w t h : ℝ}
    (he : ‖e‖ = 1) (hh : 0 < h) (hw : w ≤ t / 2)
    (hx : |inner ℝ x (perp e) - c| ≤ w) (hb : t ≤ |inner ℝ b (perp e) - c|) :
    t / (2 * h) ≤ |inner ℝ (anisotropicMap e 1 h⁻¹ x) (perp e) -
      inner ℝ (anisotropicMap e 1 h⁻¹ b) (perp e)| := by
  have htriangle : |inner ℝ b (perp e) - c| ≤
      |inner ℝ x (perp e) - inner ℝ b (perp e)| + |inner ℝ x (perp e) - c| := by
    calc |inner ℝ b (perp e) - c| =
        |(inner ℝ b (perp e) - inner ℝ x (perp e)) + (inner ℝ x (perp e) - c)| := by congr 1; ring
      _ ≤ |inner ℝ b (perp e) - inner ℝ x (perp e)| + |inner ℝ x (perp e) - c| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (inner ℝ b (perp e)) (inner ℝ x (perp e))]
  have hgap : t / 2 ≤ |inner ℝ x (perp e) - inner ℝ b (perp e)| := by linarith
  rw [(anisotropicMap_inner he 1 h⁻¹ x).2, (anisotropicMap_inner he 1 h⁻¹ b).2,
    ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hh)]
  calc t / (2 * h) = h⁻¹ * (t / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr hh.le)

theorem anisotropic_difference_norm {e b x : Plane} {c t h : ℝ}
    (he : ‖e‖ = 1) (hh : 0 < h) (hth : t ≤ h)
    (hx : |inner ℝ x (perp e) - c| ≤ t) (hb : |inner ℝ b (perp e) - c| ≤ t)
    (hfar : ‖b - x‖ ≤ 8) :
    ‖anisotropicMap e 1 h⁻¹ b - anisotropicMap e 1 h⁻¹ x‖ ≤ 10 := by
  have hn : |inner ℝ (b - x) (perp e)| ≤ 2 * h := by
    rw [inner_sub_left, show inner ℝ b (perp e) - inner ℝ x (perp e) =
      (inner ℝ b (perp e) - c) - (inner ℝ x (perp e) - c) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have heproj : |inner ℝ (b - x) e| ≤ 8 :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [he, mul_one] using hfar)
  rw [← anisotropicMap_sub]
  apply (anisotropicMap_norm_upper he 1 h⁻¹ (b - x)).trans
  rw [one_mul, abs_mul, abs_of_pos (inv_pos.mpr hh)]
  have hscaled : h⁻¹ * |inner ℝ (b - x) (perp e)| ≤ 2 := by
    calc h⁻¹ * |inner ℝ (b - x) (perp e)| ≤ h⁻¹ * (2 * h) :=
          mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hh.le)
      _ = 2 := by field_simp
  linarith

theorem anisotropic_orthogonal_norm {e a : Plane} {h : ℝ}
    (he : ‖e‖ = 1) (hh : 0 < h) (hstrip : |inner ℝ a e| ≤ h) (ha : ‖a‖ ≤ 4) :
    ‖anisotropicMap e h⁻¹ 1 a‖ ≤ 5 := by
  apply (anisotropicMap_norm_upper he h⁻¹ 1 a).trans
  rw [one_mul, abs_mul, abs_of_pos (inv_pos.mpr hh)]
  have hp : |inner ℝ a (perp e)| ≤ 4 :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [perp_norm, he, mul_one] using ha)
  have hs : h⁻¹ * |inner ℝ a e| ≤ 1 := by
    calc h⁻¹ * |inner ℝ a e| ≤ h⁻¹ * h := mul_le_mul_of_nonneg_left hstrip (inv_nonneg.mpr hh.le)
      _ = 1 := inv_mul_cancel₀ hh.ne'
  linarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
