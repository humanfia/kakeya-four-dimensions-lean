-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Freeze; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.EventGeometry

/-!
# Freezing the transverse coefficients at nearby base points

With coefficients at most `B`, base times in `[-1, 1]` and tilted transverse centers at most
`4 K²`, moving the base point by `8 K² D` (in `|Δt| + |ΔY|`) changes `transA` by at most
`110592 K¹⁰ B D` and `transB` by at most `331776 K¹⁰ B D` (for a width `|w| ≤ 1`).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

theorem agree_freeze_bounds (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) {B K : ℝ}
    (hB : 0 ≤ B) (hc : ∀ b, |G.coeff b| ≤ B) (hK1 : 1 ≤ K) (Y : ℝ → ℝ → ℝ) {w : ℝ}
    (hw : |w| ≤ 1) {t Z t' Z' D : ℝ} (ht : |t| ≤ 1) (ht' : |t'| ≤ 1)
    (hY : |Y t Z| ≤ 4 * K ^ 2) (hY' : |Y t' Z'| ≤ 4 * K ^ 2) (hD : 0 ≤ D)
    (hdist : |t - t'| + |Y t Z - Y t' Z'| ≤ 8 * K ^ 2 * D) :
    |transA G Y t Z - transA G Y t' Z'| ≤ 110592 * K ^ 10 * B * D ∧
      |transB G Y w t Z - transB G Y w t' Z'| ≤ 331776 * K ^ 10 * B * D := by
  have hR : (1 : ℝ) ≤ 4 * K ^ 2 := by nlinarith
  have hR4 : (4 * K ^ 2) ^ 4 = 256 * K ^ 8 := by ring
  have ht1 : |t| ≤ 4 * K ^ 2 := ht.trans hR
  have ht1' : |t'| ≤ 4 * K ^ 2 := ht'.trans hR
  have hA := agree_transA_sub_le G hG hB hR hc Y ht1 ht1' hY hY'
  have hBd := agree_transB_sub_le G hG hB hR hc Y ht1 ht1' hY hY' w
  rw [hR4] at hA hBd
  have hK8 : 0 ≤ K ^ 8 := by positivity
  have hBK : 0 ≤ 256 * K ^ 8 * B := by positivity
  constructor
  · calc _ ≤ 54 * B * (256 * K ^ 8) * (|t - t'| + |Y t Z - Y t' Z'|) := hA
      _ ≤ 54 * B * (256 * K ^ 8) * (8 * K ^ 2 * D) := by gcongr
      _ = 110592 * K ^ 10 * B * D := by ring
  · calc _ ≤ 162 * B * (256 * K ^ 8) * |w| * (|t - t'| + |Y t Z - Y t' Z'|) := hBd
      _ ≤ 162 * B * (256 * K ^ 8) * 1 * (8 * K ^ 2 * D) := by gcongr
      _ = 331776 * K ^ 10 * B * D := by ring

theorem agree_transB_abs_le_K (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) {B K : ℝ}
    (hB : 0 ≤ B) (hc : ∀ b, |G.coeff b| ≤ B) (hK1 : 1 ≤ K) (Y : ℝ → ℝ → ℝ) {w : ℝ}
    (hw : |w| ≤ 1) {t Z : ℝ} (ht : |t| ≤ 1) (hY : |Y t Z| ≤ 4 * K ^ 2) :
    |transB G Y w t Z| ≤ 6912 * K ^ 8 * B := by
  have hR : (1 : ℝ) ≤ 4 * K ^ 2 := by nlinarith
  have h := agree_transB_abs_le G hG hB hR hc Y w (ht.trans hR) hY
  calc _ ≤ 27 * B * (4 * K ^ 2) ^ 4 * |w| := h
    _ ≤ 27 * B * (4 * K ^ 2) ^ 4 * 1 := by gcongr
    _ = 6912 * K ^ 8 * B := by ring

theorem agree_transD_abs_le_one (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) {B : ℝ}
    (hB : 0 ≤ B) (hc : ∀ b, |G.coeff b| ≤ B) {w : ℝ} (hw : |w| ≤ 1) :
    |transD G w| ≤ 81 * B := by
  have h := agree_transD_abs_le G hG hB hc w
  have hw2 : w ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg w]
  calc _ ≤ 81 * B * w ^ 2 := h
    _ ≤ 81 * B * 1 := by gcongr
    _ = 81 * B := by ring

/-- The total freezing error of a matched pair is at most `10⁶ K¹¹ B D`. -/
theorem agree_freeze_total {K B D δ : ℝ} (hK1 : 1 ≤ K) (hB : 0 ≤ B) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hδD : δ ≤ D) {a1 b1 a2 b2 c2 d2 : ℝ}
    (ha1 : a1 ≤ 110592 * K ^ 10 * B * D) (hb1 : b1 ≤ 331776 * K ^ 10 * B * D)
    (ha2 : a2 ≤ 110592 * K ^ 10 * B * D) (hb2 : b2 ≤ 331776 * K ^ 10 * B * D)
    (hc2 : c2 ≤ 6912 * K ^ 8 * B) (hd2 : d2 ≤ 81 * B) (hc0 : 0 ≤ c2) (hd0 : 0 ≤ d2) :
    a1 + K * b1 + a2 + K * b2 + (c2 + 2 * K * d2) * δ ≤ 1000000 * K ^ 11 * B * D := by
  have hK0 : 0 ≤ K := by linarith
  have hK8 : K ^ 8 ≤ K ^ 11 := pow_le_pow_right₀ hK1 (by norm_num)
  have hK10 : K ^ 10 ≤ K ^ 11 := pow_le_pow_right₀ hK1 (by norm_num)
  have hK1' : K ≤ K ^ 11 := by
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 11 := pow_le_pow_right₀ hK1 (by norm_num)
  have hBD : 0 ≤ B * D := mul_nonneg hB hD
  have e1 : K * b1 ≤ 331776 * K ^ 11 * B * D := by
    calc K * b1 ≤ K * (331776 * K ^ 10 * B * D) := mul_le_mul_of_nonneg_left hb1 hK0
      _ = 331776 * K ^ 11 * B * D := by ring
  have e2 : K * b2 ≤ 331776 * K ^ 11 * B * D := by
    calc K * b2 ≤ K * (331776 * K ^ 10 * B * D) := mul_le_mul_of_nonneg_left hb2 hK0
      _ = 331776 * K ^ 11 * B * D := by ring
  have e3 : (c2 + 2 * K * d2) * δ ≤ 7074 * K ^ 11 * B * D := by
    have h1 : c2 + 2 * K * d2 ≤ 7074 * K ^ 11 * B := by
      have : 2 * K * d2 ≤ 2 * K * (81 * B) := mul_le_mul_of_nonneg_left hd2 (by positivity)
      have h2 : 6912 * K ^ 8 * B ≤ 6912 * K ^ 11 * B := by gcongr
      have h3 : 2 * K * (81 * B) ≤ 162 * K ^ 11 * B := by nlinarith
      linarith
    calc (c2 + 2 * K * d2) * δ ≤ (7074 * K ^ 11 * B) * D :=
          mul_le_mul h1 hδD hδ (by positivity)
      _ = 7074 * K ^ 11 * B * D := by ring
  have e4 : a1 + a2 ≤ 221184 * K ^ 11 * B * D := by
    have : 110592 * K ^ 10 * B * D ≤ 110592 * K ^ 11 * B * D := by gcongr
    linarith
  nlinarith

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
