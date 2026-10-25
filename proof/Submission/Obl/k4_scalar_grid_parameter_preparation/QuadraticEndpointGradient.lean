/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/QuadraticEndpointGradient.lean -/
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds

/-! A quadratic is controlled between two points by its endpoint gradients. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open MvPolynomial

/-- The quadratic trapezoid identity uses gradients only at the two retained points. -/
theorem quadratic_endpoint_gradient_identity (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) (x y : Fin 2 → ℝ) :
    eval y F - eval x F =
      ((y 0 - x 0) * (eval x (pderiv 0 F) + eval y (pderiv 0 F)) +
        (y 1 - x 1) * (eval x (pderiv 1 F) + eval y (pderiv 1 F))) / 2 := by
  classical
  obtain ⟨c, hc⟩ := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.isQuad2_eval F hF
  dsimp only at hc
  have hrepr : F = C (c 0) + C (c 1) * X 0 + C (c 2) * X 1 +
      C (c 3) * X 0 ^ 2 + C (c 4) * (X 0 * X 1) + C (c 5) * X 1 ^ 2 := by
    apply MvPolynomial.funext
    intro z
    have hz : (![z 0, z 1] : Fin 2 → ℝ) = z := by ext i; fin_cases i <;> rfl
    rw [← hz, hc]
    simp
  rw [hrepr]
  simp
  ring

theorem quadratic_difference_le_endpoint_gradients (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) (x y : Fin 2 → ℝ) (L : ℝ)
    (hx : ∀ e, |eval x (pderiv e F)| ≤ L)
    (hy : ∀ e, |eval y (pderiv e F)| ≤ L) :
    |eval y F - eval x F| ≤ L * (|y 0 - x 0| + |y 1 - x 1|) := by
  have h0 : |eval x (pderiv 0 F) + eval y (pderiv 0 F)| ≤ 2 * L :=
    (abs_add_le _ _).trans (by linarith [hx 0, hy 0])
  have h1 : |eval x (pderiv 1 F) + eval y (pderiv 1 F)| ≤ 2 * L :=
    (abs_add_le _ _).trans (by linarith [hx 1, hy 1])
  rw [quadratic_endpoint_gradient_identity F hF x y, abs_div,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ |y 0 - x 0| * |eval x (pderiv 0 F) + eval y (pderiv 0 F)| +
        |y 1 - x 1| * |eval x (pderiv 1 F) + eval y (pderiv 1 F)| := by
      simpa only [abs_mul] using abs_add_le
        ((y 0 - x 0) * (eval x (pderiv 0 F) + eval y (pderiv 0 F)))
        ((y 1 - x 1) * (eval x (pderiv 1 F) + eval y (pderiv 1 F)))
    _ ≤ |y 0 - x 0| * (2 * L) + |y 1 - x 1| * (2 * L) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    _ = _ := by ring

end Submission.Obl.k4_scalar_grid_parameter_preparation
