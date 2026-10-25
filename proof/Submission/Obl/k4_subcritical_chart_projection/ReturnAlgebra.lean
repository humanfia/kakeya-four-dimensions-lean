import Mathlib

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Submission.Obl.k4_subcritical_chart_projection

/-- A coarse common power controls the entire returned coefficient
expression. This permits a generous coefficient exponent fixed before losses. -/
theorem return_coefficient_expression_le {H D A B Z : ℝ}
    (hD : 0 < D) (hH : 0 ≤ H) (hA : 0 ≤ A) (hA₁ : A ≤ 1) (hB : 0 ≤ B)
    (hZ : 1 ≤ Z) (hHZ : H ≤ Z) (hHD : H / D ≤ Z) (hDi : D⁻¹ ≤ Z)
    (hBZ : B ≤ 240 * Z ^ 5) :
    6 * ((2 * (H + 2 * H / D * (2 * (H + 1) + 1))) * (1 + 2 * (H + 1))) +
      A * (9 * B * ((1 + 4 * (H + 1)) / D) ^ 2) ≤ 200000 * Z ^ 9 := by
  have hZ₀ : 0 ≤ Z := by linarith
  have hpa : 1 + 2 * (H + 1) ≤ 5 * Z := by linarith
  have hinner : 2 * (H + 1) + 1 ≤ 5 * Z := by linarith
  have hspace : 1 + 4 * (H + 1) ≤ 9 * Z := by linarith
  have hHD' : 2 * H / D ≤ 2 * Z := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hHD (by norm_num : (0 : ℝ) ≤ 2)
  have hΓ : 2 * (H + 2 * H / D * (2 * (H + 1) + 1)) ≤ 22 * Z ^ 2 := by
    calc
      _ ≤ 2 * (Z + 2 * Z * (5 * Z)) := by gcongr
      _ ≤ _ := by nlinarith
  have hratio : (1 + 4 * (H + 1)) / D ≤ 9 * Z ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (9 * Z) * Z := mul_le_mul hspace hDi (inv_nonneg.mpr hD.le) (by positivity)
      _ = _ := by ring
  have hratio₀ : 0 ≤ (1 + 4 * (H + 1)) / D := by positivity
  have hfirst : 6 * ((2 * (H + 2 * H / D * (2 * (H + 1) + 1))) *
      (1 + 2 * (H + 1))) ≤ 660 * Z ^ 3 := by
    calc
      _ ≤ 6 * ((22 * Z ^ 2) * (5 * Z)) := by gcongr
      _ = _ := by ring
  have hsecond : A * (9 * B * ((1 + 4 * (H + 1)) / D) ^ 2) ≤ 174960 * Z ^ 9 := by
    calc
      _ ≤ 1 * (9 * (240 * Z ^ 5) * (9 * Z ^ 2) ^ 2) := by gcongr
      _ = _ := by ring
  have h39 : Z ^ 3 ≤ Z ^ 9 := pow_le_pow_right₀ hZ (by decide : 3 ≤ 9)
  have hZ9 : 0 ≤ Z ^ 9 := by positivity
  nlinarith

end Submission.Obl.k4_subcritical_chart_projection
