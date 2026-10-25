-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/DiscriminantFloors.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.PolynomialSheets
import Submission.Obl.k4_paired_test_normalization.Normalization

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial

/-- The discriminant may be evaluated at the actual hidden trajectory value. -/
theorem eval_real_disc_at (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w : ℝ) :
    eval z (disc P) = (eval (Fin.snoc z w) (pderiv (3 : Fin 4) P)) ^ 2 -
      2 * Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) *
        eval (Fin.snoc z w) P := by
  rw [eval_real_disc P hP z, eval_real_hidden_derivative P hP z w,
    eval_real_hidden_quadratic P hP z w]
  ring

/-- A derivative floor and small curvature error give a signed source discriminant floor. -/
theorem disc_floor_of_derivative (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w : ℝ) {B C ρ : ℝ} (hB : 0 ≤ B)
    (hderiv : B ≤ |eval (Fin.snoc z w) (pderiv (3 : Fin 4) P)|)
    (hcurv : |Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4)| ≤ C)
    (hresid : |eval (Fin.snoc z w) P| ≤ ρ) (hsmall : 2 * C * ρ ≤ B ^ 2 / 2) :
    B ^ 2 / 2 ≤ eval z (disc P) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hcurv
  have hcross : |Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) *
      eval (Fin.snoc z w) P| ≤ C * ρ := by
    rw [abs_mul]
    exact mul_le_mul hcurv hresid (abs_nonneg _) hC
  have hs := pow_le_pow_left₀ hB hderiv 2
  rw [sq_abs] at hs
  rw [eval_real_disc_at P hP z w]
  nlinarith [le_abs_self (Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) *
    eval (Fin.snoc z w) P)]

/-- Every active label has enough coefficient size to apply normalized sublevel deletion. -/
theorem coefficientSize_floor_at_regular_source (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (z : EuclideanSpace ℝ (Fin 3)) (hz : ‖z‖ ≤ 1)
    (w : ℝ) {B C ρ : ℝ} (hB : 0 ≤ B)
    (hderiv : B ≤ |eval (Fin.snoc (fun i => z i) w) (pderiv (3 : Fin 4) P)|)
    (hcurv : |Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4)| ≤ C)
    (hresid : |eval (Fin.snoc (fun i => z i) w) P| ≤ ρ)
    (hsmall : 2 * C * ρ ≤ B ^ 2 / 2) : B ^ 2 / 2 ≤ coefficientSize (disc P) := by
  have hD := disc_floor_of_derivative P hP (fun i => z i) w hB hderiv hcurv hresid hsmall
  exact hD.trans ((le_abs_self _).trans
    (abs_eval_le_coefficientSize (disc P) (fun i => z i)
      (fun i => (PiLp.norm_apply_le z i).trans hz)))

end Submission.Obl.k4_paired_test_normalization
