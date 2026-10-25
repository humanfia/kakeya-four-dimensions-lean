-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AlignmentScales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AlignmentBudget
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CircleGeometry

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem AlignmentScaleBudget.inverse_scale {δ ε η κ : ℝ}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ) (hε : 0 ≤ ε) :
    32 ≤ δ ^ (-ε + κ) := by
  have hsmall : δ ^ (ε / 2) ≤ 1 := Real.rpow_le_one hδ.le hb.scale_le_one (by linarith)
  have hnum : 32 * δ ^ (ε - κ) ≤ 1 := hb.radial_scale.trans hsmall
  have hid : δ ^ (-ε + κ) = 1 / δ ^ (ε - κ) := by
    rw [show -ε + κ = -(ε - κ) by ring, Real.rpow_neg hδ.le, one_div]
  rw [hid]
  exact (le_div_iff₀ (by positivity : 0 < δ ^ (ε - κ))).mpr hnum

theorem AlignmentScaleBudget.inverse_epsilon {δ ε η κ : ℝ}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ) :
    32 ≤ δ ^ (-ε) :=
  (hb.inverse_scale hδ hε).trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hb.scale_le_one (by linarith))

theorem AlignmentScaleBudget.narrow_relative_width {δ ε η κ w t : ℝ}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ) (hε : 0 ≤ ε) (hw : 0 < w)
    (hlarge : δ ^ (-ε + κ) * w < t) : w ≤ t / 2 := by
  have h := mul_le_mul_of_nonneg_right (hb.inverse_scale hδ hε) hw.le
  linarith

theorem AlignmentScaleBudget.wide_radial_scale {δ ε η κ w t : ℝ}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ) (hε : 0 ≤ ε) (hw : 0 < w)
    (ht16 : t ≤ 16) (hlarge : δ ^ (-ε + κ) * w < t) :
    2 * w ≤ 1 ∧ δ ^ (-ε / 2) ≤ 1 / w := by
  have hwbound : w ≤ δ ^ (ε - κ) * t := by
    calc w = δ ^ (ε - κ) * (δ ^ (-ε + κ) * w) := by
          rw [← mul_assoc, ← Real.rpow_add hδ]
          simp only [show ε - κ + (-ε + κ) = 0 by ring, Real.rpow_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlarge.le (by positivity)
  have h16 : w ≤ 16 * δ ^ (ε - κ) :=
    hwbound.trans (by nlinarith [mul_le_mul_of_nonneg_left ht16 (by positivity : 0 ≤ δ ^ (ε - κ))])
  have hsmall : δ ^ (ε / 2) ≤ 1 := Real.rpow_le_one hδ.le hb.scale_le_one (by linarith)
  have h2w : 2 * w ≤ δ ^ (ε / 2) := by linarith [hb.radial_scale]
  refine ⟨h2w.trans hsmall, ?_⟩
  apply (le_div_iff₀ hw).mpr
  calc δ ^ (-ε / 2) * w ≤ δ ^ (-ε / 2) * δ ^ (ε / 2) :=
        mul_le_mul_of_nonneg_left (by linarith : w ≤ δ ^ (ε / 2)) (by positivity)
    _ = 1 := by rw [← Real.rpow_add hδ, show -ε / 2 + ε / 2 = 0 by ring, Real.rpow_zero]

theorem AlignmentScaleBudget.anisotropic_radial_scale {δ ε η κ w t : ℝ}
    (hb : AlignmentScaleBudget δ ε η κ) (hδ : 0 < δ) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (hw : 0 < w) (ht : 0 < t) (hlarge : δ ^ (-ε + κ) * w < t) :
    2 * w / (δ ^ (-κ) * t) ≤ 1 ∧ δ ^ (-ε / 2) ≤ (δ ^ (-κ) * t) / w := by
  have hbig : δ ^ (-ε) * w ≤ δ ^ (-κ) * t := by
    calc δ ^ (-ε) * w = δ ^ (-κ) * (δ ^ (-ε + κ) * w) := by
          rw [← mul_assoc, ← Real.rpow_add hδ]
          congr 1
          congr 1
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlarge.le (by positivity)
  have h32 := mul_le_mul_of_nonneg_right (hb.inverse_epsilon hδ hε hκ) hw.le
  refine ⟨(div_le_one (by positivity : 0 < δ ^ (-κ) * t)).mpr (by linarith), ?_⟩
  apply (le_div_iff₀ hw).mpr
  have hpow : δ ^ (-ε / 2) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hb.scale_le_one (by linarith)
  exact (mul_le_mul_of_nonneg_right hpow hw.le).trans hbig

theorem strip_height_bound {n x b : Plane} {c w : ℝ} (hn : ‖n‖ = 1)
    (hx : ‖x‖ ≤ 4) (hb : ‖b‖ ≤ 4) (hstrip : |inner ℝ x n - c| ≤ w) :
    |inner ℝ b n - c| ≤ 8 + w := by
  have hdiff : |inner ℝ b n - inner ℝ x n| ≤ 8 := by
    rw [← inner_sub_left]
    calc |inner ℝ (b - x) n| ≤ ‖b - x‖ * ‖n‖ := abs_real_inner_le_norm _ _
      _ = ‖b - x‖ := by rw [hn, mul_one]
      _ ≤ ‖b‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 8 := by linarith
  calc |inner ℝ b n - c| = |(inner ℝ b n - inner ℝ x n) + (inner ℝ x n - c)| := by congr 1; ring
    _ ≤ |inner ℝ b n - inner ℝ x n| + |inner ℝ x n - c| := abs_add_le _ _
    _ ≤ _ := by linarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
