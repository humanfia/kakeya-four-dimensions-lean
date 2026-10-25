-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.StretchSeparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Geometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Basic

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open LeanEval.Analysis.WangZahlKakeya
open wz_affine_robust_cluster_estimate

/-- Adding a multiple of one vector to the other does not change their area. -/
theorem areaSq_sub_smul (q v : Space) (s : ℝ) :
    areaSq (q - s • v) v = areaSq q v := by
  simp only [areaSq, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- For a unit vector, parallelogram area is squared perpendicular distance. -/
theorem perpendicular_norm_sq {v : Space} (hv : ‖v‖ = 1) (q : Space) :
    ‖q - (inner ℝ v q) • v‖ ^ 2 = areaSq q v := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs,
    real_inner_smul_right, real_inner_comm q v, areaSq_gram, hv]
  ring

/-- A transverse stretch expands distance from any line whose stretched unit
direction has bounded length. This also controls the position parameters of
tubes after affine rescaling. -/
theorem perpendicular_distance_of_stretched_line_error {t L r : ℝ}
    (ht : 1 ≤ t) (hr : 0 ≤ r) {v q : Space} (hv : ‖v‖ = 1)
    (hL : ‖stretch t v‖ ≤ L) {s : ℝ}
    (herror : ‖stretch t q - s • unit (stretch t v)‖ ≤ r) :
    ‖q - (inner ℝ v q) • v‖ ≤ L * r / t := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hLpos : 0 ≤ L := (norm_nonneg _).trans hL
  have heq : areaSq (stretch t q - s • unit (stretch t v)) (stretch t v) =
      areaSq (stretch t q) (stretch t v) := by
    unfold unit
    rw [smul_smul]
    exact areaSq_sub_smul _ _ _
  have hupper : areaSq (stretch t q) (stretch t v) ≤ r ^ 2 * L ^ 2 := by
    rw [← heq]
    calc
      _ ≤ ‖stretch t q - s • unit (stretch t v)‖ ^ 2 * ‖stretch t v‖ ^ 2 := by
        rw [areaSq_gram]
        exact sub_le_self _ (sq_nonneg _)
      _ ≤ r ^ 2 * L ^ 2 := mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) herror 2)
        (pow_le_pow_left₀ (norm_nonneg _) hL 2) (sq_nonneg _) (sq_nonneg _)
  have hscale := areaSq_stretch ht q v
  rw [← perpendicular_norm_sq hv q] at hscale
  have hsq : (t * ‖q - (inner ℝ v q) • v‖) ^ 2 ≤ (L * r) ^ 2 := by
    nlinarith only [hscale, hupper]
  apply (le_div_iff₀ htpos).mpr
  nlinarith [norm_nonneg (q - (inner ℝ v q) • v), mul_nonneg hLpos hr]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
