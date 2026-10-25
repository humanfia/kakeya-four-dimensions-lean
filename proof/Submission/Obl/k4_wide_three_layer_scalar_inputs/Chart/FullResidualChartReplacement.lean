/- Adapted from this LOT tree o218, branch x0760, commit 5db19453bd17cc371d54c5ac350db64cdc0ec595,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/FullResidualChartReplacement.lean. Original attribution, when present, is preserved below. -/

import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.PhysicalChartReplacement

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MvPolynomial

/-- A physical quadratic varies in Y with its original coefficient bound. -/
theorem physical_quadratic_y_difference_bound (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) {B H t Y Y' : ℝ}
    (hcoef : ∀ d, |P.coeff d| ≤ B) (hH : 1 ≤ H)
    (ht : |t| ≤ 1) (hY : |Y| ≤ H) (hY' : |Y'| ≤ 3 * H) :
    |eval ![t, Y] P - eval ![t, Y'] P| ≤ 6 * B * H * |Y - Y'| := by
  obtain ⟨G, hG⟩ := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.isQuad2_eval P hP
  dsimp only at hG
  have hc := quadratic_representation_coeff_bound P G hG hcoef
  have hB : 0 ≤ B := (abs_nonneg _).trans (hc 0)
  have hH0 : 0 ≤ H := by linarith
  have hGt : |G 4 * t| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (hc 4) ht (abs_nonneg _) hB).trans_eq (mul_one _)
  have hGY : |G 5 * (Y + Y')| ≤ 4 * B * H := by
    rw [abs_mul]
    have hh : |Y + Y'| ≤ 4 * H := (abs_add_le _ _).trans (by linarith)
    exact (mul_le_mul (hc 5) hh (abs_nonneg _) hB).trans_eq (by ring)
  have hfactor : |G 2 + G 4 * t + G 5 * (Y + Y')| ≤ 6 * B * H := by
    calc
      _ ≤ |G 2| + |G 4 * t| + |G 5 * (Y + Y')| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ B + B + 4 * B * H := add_le_add (add_le_add (hc 2) hGt) hGY
      _ ≤ _ := by nlinarith [mul_nonneg hB (sub_nonneg.mpr hH)]
  have hid : eval ![t, Y] P - eval ![t, Y'] P =
      (G 2 + G 4 * t + G 5 * (Y + Y')) * (Y - Y') := by
    rw [hG, hG]
    ring
  rw [hid, abs_mul]
  exact mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)

/-- The full original residual, before freezing its intercept onto a key chart. -/
noncomputable def physicalResidual (P : MvPolynomial (Fin 2) ℝ) (L : Fin 4 → ℝ)
    (a t Z Y : ℝ) : ℝ :=
  (eval ![t, Y] P - (L 0 + L 1 * t + L 2 * Z + L 3 * Y)) / a

/-- Freeze the ENTIRE residual while preserving its actual transverse coordinate:
Yalpha=Y-c4*(Z-Zalpha). Only physical P coefficients and the native slopes enter. -/
theorem physicalResidual_chart_error (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (L : Fin 4 → ℝ)
    {a t Z Z' Y tilt H B Lb δ : ℝ}
    (ha : 0 < a) (hH : 1 ≤ H)
    (hcoef : ∀ d, |P.coeff d| ≤ B)
    (hL2 : |L 2| ≤ Lb) (hL3 : |L 3| ≤ Lb)
    (ht : |t| ≤ 1) (hY : |Y| ≤ H) (htilt : |tilt| ≤ H)
    (hZ : |Z - Z'| ≤ δ) (hδ : δ ≤ 2) :
    |physicalResidual P L a t Z Y -
      physicalResidual P L a t Z' (Y - tilt * (Z - Z'))| ≤
      (6 * B * H ^ 2 + 2 * Lb * H) * δ / a := by
  let Y' := Y - tilt * (Z - Z')
  have hH0 : 0 ≤ H := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hcoef 0)
  have hLb : 0 ≤ Lb := (abs_nonneg _).trans hL2
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hZ
  have hdy : |Y - Y'| ≤ H * δ := by
    have heq : Y - Y' = tilt * (Z - Z') := by dsimp only [Y']; ring
    rw [heq, abs_mul]
    exact mul_le_mul htilt hZ (abs_nonneg _) hH0
  have hY' : |Y'| ≤ 3 * H := by
    calc
      _ ≤ |Y| + |tilt * (Z - Z')| := abs_sub _ _
      _ = |Y| + |Y - Y'| := by dsimp only [Y']; congr 2; ring
      _ ≤ H + H * δ := add_le_add hY hdy
      _ ≤ _ := by nlinarith
  have hnative : |L 2 * (Z - Z') + L 3 * (Y - Y')| ≤ 2 * Lb * H * δ := by
    calc
      _ ≤ |L 2| * |Z - Z'| + |L 3| * |Y - Y'| := by
        simpa only [abs_mul] using abs_add_le (L 2 * (Z - Z')) (L 3 * (Y - Y'))
      _ ≤ Lb * δ + Lb * (H * δ) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hLb hδ0) (sub_nonneg.mpr hH)]
  have hPe := physical_quadratic_y_difference_bound P hP hcoef hH ht hY hY'
  have hid : physicalResidual P L a t Z Y - physicalResidual P L a t Z' Y' =
      ((eval ![t, Y] P - eval ![t, Y'] P) -
        (L 2 * (Z - Z') + L 3 * (Y - Y'))) / a := by
    simp only [physicalResidual, div_eq_mul_inv]
    ring
  change |physicalResidual P L a t Z Y - physicalResidual P L a t Z' Y'| ≤ _
  rw [hid, abs_div, abs_of_pos ha]
  apply div_le_div_of_nonneg_right _ ha.le
  calc
    _ ≤ |eval ![t, Y] P - eval ![t, Y'] P| +
        |L 2 * (Z - Z') + L 3 * (Y - Y')| := abs_sub _ _
    _ ≤ 6 * B * H * |Y - Y'| + 2 * Lb * H * δ := add_le_add hPe hnative
    _ ≤ 6 * B * H * (H * δ) + 2 * Lb * H * δ := by gcongr
    _ = _ := by ring

/-- The actual fixed-power physical/native bounds pay the FULL residual
replacement error, uniformly over the arbitrarily small geometric loss. -/
theorem eventually_full_residual_chart_replacement
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Filter.Tendsto N Filter.atTop Filter.atTop)
    {s₀ sp M : ℝ} (hs₀ : 0 < s₀) (hsp : sp < 3 * s₀ / 2)
    (hM : 100 * s₀ < M) :
    ∀ᶠ k in Filter.atTop, ∀ η : ℝ, 0 ≤ η → η ≤ s₀ →
      ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ 2 →
      ∀ L : Fin 4 → ℝ,
      (∀ d, |P.coeff d| ≤ N k ^ (10 * s₀)) →
      |L 2| ≤ N k ^ (5 * s₀) → |L 3| ≤ N k ^ (5 * s₀) →
      ∀ t Z Z' Y tilt : ℝ, |t| ≤ 1 → |Y| ≤ N k ^ η →
      |tilt| ≤ N k ^ η → |Z - Z'| ≤ 2 * N k ^ (-M) →
      |physicalResidual P L (N k ^ (-sp)) t Z Y -
        physicalResidual P L (N k ^ (-sp)) t Z' (Y - tilt * (Z - Z'))| ≤
          N k ^ (-M / 2) := by
  have hgrowth := (tendsto_rpow_atTop hs₀).comp hNt
  filter_upwards [hgrowth.eventually (Filter.eventually_ge_atTop (16 : ℝ))] with k hk
  change 16 ≤ N k ^ s₀ at hk
  intro η hη0 hη P hP L hcoef hL2 hL3 t Z Z' Y tilt ht hY htilt hZ
  have hNk : 1 ≤ N k := by linarith [hN k]
  have hNk0 : 0 < N k := by linarith
  have ha : 0 < N k ^ (-sp) := Real.rpow_pos_of_pos hNk0 _
  have hM0 : 0 < M := by linarith
  have hδ : 2 * N k ^ (-M) ≤ 2 := by
    have hh := Real.rpow_le_one_of_one_le_of_nonpos hNk (show -M ≤ 0 by linarith)
    linarith
  have herr := physicalResidual_chart_error P hP L ha (Real.one_le_rpow hNk hη0)
    hcoef hL2 hL3 ht hY htilt hZ hδ
  have hηpow : N k ^ η ≤ N k ^ s₀ :=
    Real.rpow_le_rpow_of_exponent_le hNk hη
  have h12 : N k ^ (10 * s₀) * (N k ^ s₀) ^ 2 = N k ^ (12 * s₀) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNk0.le, ← Real.rpow_add hNk0]
    congr 1 <;> ring
  have h6 : N k ^ (5 * s₀) * N k ^ s₀ = N k ^ (6 * s₀) := by
    rw [← Real.rpow_add hNk0]
    congr 1 <;> ring
  have h6le : N k ^ (6 * s₀) ≤ N k ^ (12 * s₀) :=
    Real.rpow_le_rpow_of_exponent_le hNk (by linarith)
  have hnum : 6 * N k ^ (10 * s₀) * (N k ^ η) ^ 2 +
      2 * N k ^ (5 * s₀) * N k ^ η ≤ 8 * N k ^ (12 * s₀) := by
    calc
      _ ≤ 6 * N k ^ (10 * s₀) * (N k ^ s₀) ^ 2 +
          2 * N k ^ (5 * s₀) * N k ^ s₀ := by gcongr
      _ = 6 * N k ^ (12 * s₀) + 2 * N k ^ (6 * s₀) := by
        calc
          _ = 6 * (N k ^ (10 * s₀) * (N k ^ s₀) ^ 2) +
              2 * (N k ^ (5 * s₀) * N k ^ s₀) := by ring
          _ = _ := by rw [h12, h6]
      _ ≤ _ := by linarith
  calc
    _ ≤ (6 * N k ^ (10 * s₀) * (N k ^ η) ^ 2 +
        2 * N k ^ (5 * s₀) * N k ^ η) * (2 * N k ^ (-M)) / N k ^ (-sp) := herr
    _ ≤ (8 * N k ^ (12 * s₀)) * (2 * N k ^ (-M)) / N k ^ (-sp) := by gcongr
    _ = 16 * N k ^ (12 * s₀ - M + sp) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hNk0.le, neg_neg]
      calc
        _ = 16 * (N k ^ (12 * s₀) * N k ^ (-M) * N k ^ sp) := by ring
        _ = _ := by rw [← Real.rpow_add hNk0, ← Real.rpow_add hNk0, sub_eq_add_neg]
    _ ≤ N k ^ s₀ * N k ^ (12 * s₀ - M + sp) := by gcongr
    _ = N k ^ (s₀ + (12 * s₀ - M + sp)) := (Real.rpow_add hNk0 _ _).symm
    _ ≤ N k ^ (-M / 2) := Real.rpow_le_rpow_of_exponent_le hNk (by linarith)

end Submission.Obl.k4_wide_three_layer_scalar_inputs
