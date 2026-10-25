-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.PolynomialCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Definitions
import Submission.WZ.Obl.wz_multiscale_finite_tower.Elementary

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (A)

/-- The normalized convex count bounds the number of fine tubes by a fixed
polynomial, so logarithmic multiplicity selection costs a small power. -/
theorem normalized_polynomial_count {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (hη : η ≤ 1) {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hA : A δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y) : (n : ℝ) ≤ δ ^ (-(4 : ℝ)) := by
  have hframe : wz_multiscale_finite_tower.FrameAdmissible δ δ η n x v Y := hA
  have hc := hframe.card_bound hδ
  have hp : δ ^ (-η) ≤ δ ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) (by linarith)
  rw [Real.rpow_neg_one] at hp
  have hb : (n : ℝ) * δ ^ 3 ≤ 16 := by
    calc
      _ = ((n : ℝ) * δ ^ 2) * δ := by ring
      _ ≤ (16 * δ⁻¹) * δ := mul_le_mul_of_nonneg_right
        (hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num))) hδ.le
      _ = _ := by rw [mul_assoc, inv_mul_cancel₀ hδ.ne', mul_one]
  have hfour : (n : ℝ) * δ ^ 4 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hb hδ.le
    nlinarith
  calc
    _ ≤ 1 / δ ^ 4 := (le_div_iff₀ (pow_pos hδ 4)).mpr hfour
    _ = _ := by rw [Real.rpow_neg hδ.le]; norm_num [one_div]

end WangZahlLot.Obl.wz_broad_grains_initialization
