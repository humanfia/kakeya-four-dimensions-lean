import Submission.Obl.k4_scalar_candidate_original_return.Core.QuadBounds

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MvPolynomial

/-- The difference of a quadratic is the average endpoint gradient paired with displacement. -/
theorem quadratic_gradient_mean_identity (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) (z z' : Fin 2 → ℝ) :
    eval z F - eval z' F =
      ((z 0 - z' 0) * (eval z (pderiv 0 F) + eval z' (pderiv 0 F)) +
        (z 1 - z' 1) * (eval z (pderiv 1 F) + eval z' (pderiv 1 F))) / 2 := by
  obtain ⟨a, b, c, d, e, f, hnf⟩ :=
    Submission.Obl.k4_scalar_candidate_original_return.QuadBounds.quad_normal_form F hF
  have heq : F = C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
      C e * X 0 * X 1 + C f * X 1 ^ 2 := by
    apply MvPolynomial.funext
    intro w
    rw [hnf]
    simp
  rw [heq]
  simp
  ring

/-- Low-gradient points on a quadratic graph are mutually Lipschitz, even if
only the two actual endpoint gradients are known to be small. -/
theorem quadratic_lipschitz_between_low_gradient_points (F : MvPolynomial (Fin 2) ℝ)
    (hF : F.totalDegree ≤ 2) (z z' : Fin 2 → ℝ) {H : ℝ}
    (hz : ∀ e, |eval z (pderiv e F)| ≤ H)
    (hz' : ∀ e, |eval z' (pderiv e F)| ≤ H) :
    |eval z F - eval z' F| ≤ H * (|z 0 - z' 0| + |z 1 - z' 1|) := by
  rw [quadratic_gradient_mean_identity F hF z z', abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have hterm (e : Fin 2) :
      |(z e - z' e) * (eval z (pderiv e F) + eval z' (pderiv e F))| ≤
        2 * H * |z e - z' e| := by
    rw [abs_mul]
    calc
      _ ≤ |z e - z' e| * (|eval z (pderiv e F)| + |eval z' (pderiv e F)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ ≤ |z e - z' e| * (H + H) :=
        mul_le_mul_of_nonneg_left (add_le_add (hz e) (hz' e)) (abs_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ |(z 0 - z' 0) * (eval z (pderiv 0 F) + eval z' (pderiv 0 F))| +
        |(z 1 - z' 1) * (eval z (pderiv 1 F) + eval z' (pderiv 1 F))| := abs_add_le _ _
    _ ≤ 2 * H * |z 0 - z' 0| + 2 * H * |z 1 - z' 1| := add_le_add (hterm 0) (hterm 1)
    _ = _ := by ring

end Submission.Obl.k4_scalar_grid_cartesian_field
