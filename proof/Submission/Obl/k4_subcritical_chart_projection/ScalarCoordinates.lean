import Submission.Obl.k4_subcritical_chart_projection.Model
import Submission.Obl.k4_horizontal_supercritical_three_projections.NormalizedScalar

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- The corrected signal is affine in time, and its parameter is the
horizontal scalar coordinate supplied by the chart. -/
def scalarCoefficients (D a : ℝ) (P Q : ℤ) (g b : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![chartQ D Q b, -2 * chartP D P b,
    (b 2 - g 0 - g 2 * b 0 - g 4 * b 1) / a,
    (b 5 - g 1 - g 3 * b 0 - g 5 * b 1) / a, 0]

theorem scalarCoefficients_y (D a : ℝ) (P Q : ℤ) (g b : Fin 6 → ℝ) (t : ℝ) :
    scalarY (scalarCoefficients D a P Q g b) t = chartR D P Q b t := by
  simp only [scalarY, scalarCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one,
    chartR]
  ring

theorem scalarCoefficients_x (D a : ℝ) (P Q : ℤ) (g b : Fin 6 → ℝ) (t : ℝ) :
    scalarX (scalarCoefficients D a P Q g b) t = chartSignal a g b t := by
  simp only [scalarX, scalarCoefficients, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, chartSignal, predictor,
    Submission.Lib.K4FullTimeLayers.parameterPredictor]
  ring

theorem scalarCoefficients_cell (D a σ : ℝ) (P Q : ℤ) (g b : Fin 6 → ℝ) (t : ℝ) :
    scalarCell (scalarCoefficients D a P Q g b) t σ = chartCell D σ P Q b t := by
  simp only [scalarCell, scalarCoefficients_y, chartCell]

theorem measurable_scalarCoefficients {α : Type} [MeasurableSpace α]
    (D a : ℝ) (P Q : ℤ) (g : Fin 6 → ℝ)
    (b : α → Fin 6 → ℝ) (hb : Measurable b) :
    Measurable (fun l => scalarCoefficients D a P Q g (b l)) := by
  apply Measurable.of_eval
  intro e
  fin_cases e <;> simp only [scalarCoefficients, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one, chartP, chartQ] <;> fun_prop

/-- The full-time corrected signal bound controls its two coefficients;
there is no division by the small physical signal scale in this estimate. -/
theorem scalarCoefficients_bound {D a H : ℝ} {P Q : ℤ} {g b : Fin 6 → ℝ}
    (hD : 0 < D) (hH : 1 ≤ H)
    (hp : ⌊b 0 / D⌋ = P) (hq : ⌊b 1 / D⌋ = Q)
    (hsignal : ∀ t ∈ Icc (0 : ℝ) 1, |chartSignal a g b t| ≤ H) :
    ∀ e, |scalarCoefficients D a P Q g b e| ≤ 2 * H := by
  have hq₀ : 0 ≤ chartQ D Q b := by
    unfold chartQ
    have hh := (le_div_iff₀ hD).mp (Int.floor_le (b 1 / D))
    rw [hq] at hh
    exact div_nonneg (by linarith) hD.le
  have hq₁ : chartQ D Q b ≤ 1 := by
    unfold chartQ
    have hh := (div_lt_iff₀ hD).mp (Int.lt_floor_add_one (b 1 / D))
    rw [hq] at hh
    apply (div_le_iff₀ hD).mpr
    linarith
  have hp₀ : 0 ≤ chartP D P b := by
    unfold chartP
    have hh := (le_div_iff₀ hD).mp (Int.floor_le (b 0 / D))
    rw [hp] at hh
    exact div_nonneg (by linarith) hD.le
  have hp₁ : chartP D P b ≤ 1 := by
    unfold chartP
    have hh := (div_lt_iff₀ hD).mp (Int.lt_floor_add_one (b 0 / D))
    rw [hp] at hh
    apply (div_le_iff₀ hD).mpr
    linarith
  have hb₂ : |scalarCoefficients D a P Q g b 2| ≤ H := by
    simpa only [← scalarCoefficients_x D a P Q g b 0, scalarX,
      mul_zero, zero_mul, zero_add, zero_pow (by norm_num : 2 ≠ 0), add_zero] using hsignal 0 (by norm_num)
  have hb₃ : |scalarCoefficients D a P Q g b 3| ≤ 2 * H := by
    have h1 := hsignal 1 (by norm_num)
    have h0 := hsignal 0 (by norm_num)
    calc
      _ = |chartSignal a g b 1 - chartSignal a g b 0| := by
        rw [← scalarCoefficients_x D a P Q g b 1, ← scalarCoefficients_x D a P Q g b 0]
        simp [scalarX, scalarCoefficients]
      _ ≤ |chartSignal a g b 1| + |chartSignal a g b 0| := abs_sub _ _
      _ ≤ _ := by linarith
  intro e
  fin_cases e
  · change |chartQ D Q b| ≤ 2 * H
    rw [abs_of_nonneg hq₀]
    linarith
  · change |-2 * chartP D P b| ≤ 2 * H
    rw [abs_mul, abs_of_nonneg hp₀]
    norm_num
    linarith
  · exact hb₂.trans (by linarith)
  · exact hb₃
  · change |(0 : ℝ)| ≤ 2 * H
    rw [abs_zero]
    linarith

end
end Submission.Obl.k4_subcritical_chart_projection
