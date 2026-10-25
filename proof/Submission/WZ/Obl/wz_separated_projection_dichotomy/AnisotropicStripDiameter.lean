-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AnisotropicStripDiameter.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AnisotropicNormal
import Submission.WZ.Obl.wz_separated_projection_dichotomy.StripProjectionGeometry

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- A strip with nearly longitudinal normal pulls back to a small set when
both the original band and the output strip are narrow. -/
theorem anisotropic_parallel_strip_diameter {e n x y : Plane} {h q r c d : ℝ}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hh : 0 < h) (hhq : h ≤ q) (hq : q ≤ 1 / 2)
    (hrq : r ≤ q) (hnperp : |inner ℝ n (perp e)| ≤ q)
    (hx : |inner ℝ x (perp e) - c| ≤ h) (hy : |inner ℝ y (perp e) - c| ≤ h)
    (hTx : |inner ℝ (anisotropicMap e 1 h⁻¹ x) n - d| ≤ r)
    (hTy : |inner ℝ (anisotropicMap e 1 h⁻¹ y) n - d| ≤ r) :
    dist x y ≤ 10 * q := by
  have hqpos : 0 < q := hh.trans_le hhq
  have hne : 1 / 2 ≤ |inner ℝ n e| := by
    have hid := inner_sq_add_perp_inner_sq n e
    rw [he, hn] at hid
    have hnp : |inner ℝ n (perp e)| ≤ 1 / 2 := hnperp.trans hq
    nlinarith [sq_abs (inner ℝ n e), sq_abs (inner ℝ n (perp e)),
      abs_nonneg (inner ℝ n e), abs_nonneg (inner ℝ n (perp e))]
  have hdn := strip_difference_perp hx hy
  have houtput : |inner ℝ (anisotropicMap e 1 h⁻¹ x) n -
      inner ℝ (anisotropicMap e 1 h⁻¹ y) n| ≤ 2 * q := by
    have hid : inner ℝ (anisotropicMap e 1 h⁻¹ x) n - inner ℝ (anisotropicMap e 1 h⁻¹ y) n =
        (inner ℝ (anisotropicMap e 1 h⁻¹ x) n - d) -
          (inner ℝ (anisotropicMap e 1 h⁻¹ y) n - d) := by ring
    rw [hid]
    exact (abs_sub _ _).trans (by linarith)
  have hid : inner ℝ n e * inner ℝ (x - y) e =
      (inner ℝ (anisotropicMap e 1 h⁻¹ x) n - inner ℝ (anisotropicMap e 1 h⁻¹ y) n) -
        (h⁻¹ * inner ℝ (x - y) (perp e)) * inner ℝ n (perp e) := by
    rw [← inner_sub_left, ← anisotropicMap_sub,
      inner_eq_frame_sum he (anisotropicMap e 1 h⁻¹ (x - y)) n,
      (anisotropicMap_inner he 1 h⁻¹ (x - y)).1, (anisotropicMap_inner he 1 h⁻¹ (x - y)).2]
    ring
  have herr : |(h⁻¹ * inner ℝ (x - y) (perp e)) * inner ℝ n (perp e)| ≤ 2 * q := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hh)]
    calc h⁻¹ * |inner ℝ (x - y) (perp e)| * |inner ℝ n (perp e)| ≤ h⁻¹ * (2 * h) * q := by gcongr
      _ = _ := by field_simp
  have hde : |inner ℝ n e| * |inner ℝ (x - y) e| ≤ 4 * q := by
    rw [← abs_mul, hid]
    exact (abs_sub _ _).trans (by linarith)
  have hde' : |inner ℝ (x - y) e| ≤ 8 * q := by
    nlinarith [mul_le_mul_of_nonneg_right hne (abs_nonneg (inner ℝ (x - y) e))]
  rw [dist_eq_norm]
  exact (norm_le_frame_sum he (x - y)).trans (by linarith)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
