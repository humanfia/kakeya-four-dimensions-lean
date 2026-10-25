-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.UnitTransport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Geometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Metric
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (E unit norm_unit pd pd_nonneg)

lemma unit_neg (v : E) : unit (-v) = -unit v := by simp [unit]

lemma unit_pos_smul {s : ℝ} (hs : 0 < s) (v : E) : unit (s • v) = unit v := by
  by_cases hv : v = 0
  · simp [hv, unit]
  · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [unit, norm_smul, Real.norm_eq_abs, abs_of_pos hs, smul_smul]
    simp [unit, mul_inv, hs.ne', mul_assoc]

/-- Normalizing vectors is quantitatively continuous away from zero. -/
lemma unit_sub_norm_le {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖unit u - unit v‖ ≤ 2 * ‖u - v‖ / ‖u‖ := by
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have he : unit u - unit v = ‖u‖⁻¹ • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹) • v := by
    dsimp [unit]
    module
  have hcoef : |‖u‖⁻¹ - ‖v‖⁻¹| * ‖v‖ = |‖v‖ - ‖u‖| / ‖u‖ := by
    rw [show ‖u‖⁻¹ - ‖v‖⁻¹ = (‖v‖ - ‖u‖) / (‖u‖ * ‖v‖) by field_simp,
      abs_div, abs_mul, abs_of_pos hu0, abs_of_pos hv0]
    field_simp
  have hnormdiff : |‖v‖ - ‖u‖| ≤ ‖u - v‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le v u
  rw [he]
  calc
    _ ≤ ‖‖u‖⁻¹ • (u - v)‖ + ‖(‖u‖⁻¹ - ‖v‖⁻¹) • v‖ := norm_add_le _ _
    _ = ‖u - v‖ / ‖u‖ + |‖v‖ - ‖u‖| / ‖u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hu0), hcoef]
      ring
    _ ≤ ‖u - v‖ / ‖u‖ + ‖u - v‖ / ‖u‖ :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hnormdiff hu0.le)
    _ = _ := by ring

lemma unit_linear_sub_le (A : E →ₗ[ℝ] E) {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hA : ∀ p, ‖A p‖ ≤ C * ‖p‖) {u v : E}
    (hu : a ≤ ‖A u‖) (hv : A v ≠ 0) :
    ‖unit (A u) - unit (A v)‖ ≤ (2 * C / a) * ‖u - v‖ := by
  have hu0 : 0 < ‖A u‖ := ha.trans_le hu
  calc
    _ ≤ 2 * ‖A u - A v‖ / ‖A u‖ := unit_sub_norm_le (norm_pos_iff.mp hu0) hv
    _ ≤ 2 * (C * ‖u - v‖) / ‖A u‖ := by
      apply div_le_div_of_nonneg_right _ hu0.le
      rw [← map_sub]
      exact mul_le_mul_of_nonneg_left (hA (u - v)) (by norm_num)
    _ ≤ 2 * (C * ‖u - v‖) / a := div_le_div_of_nonneg_left (by positivity) ha hu
    _ = _ := by ring

lemma unit_linear_pd_le (A : E →ₗ[ℝ] E) {C a : ℝ} (hC : 0 ≤ C) (ha : 0 < a)
    (hA : ∀ p, ‖A p‖ ≤ C * ‖p‖) {u v : E}
    (hu : a ≤ ‖A u‖) (hv : A v ≠ 0) :
    pd (unit (A u)) (unit (A v)) ≤ (2 * C / a) * pd u v := by
  have hs := unit_linear_sub_le A hC ha hA hu hv
  have hp := unit_linear_sub_le A hC ha hA hu (v := -v) (by simpa using hv)
  rw [map_neg, unit_neg, sub_neg_eq_add, sub_neg_eq_add] at hp
  unfold pd
  rcases le_total ‖u - v‖ ‖u + v‖ with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hs
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans hp

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
