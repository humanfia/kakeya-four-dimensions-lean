import Submission.Obl.k4_stable_quadratic_hidden_sheets.Variation
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Sheet

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MvPolynomial

theorem quadratic_background_variation
    (P : MvPolynomial (Fin 3) ℝ) (hP : P.totalDegree ≤ 2)
    {M R δ : ℝ} (hM : ∀ e, |P.coeff e| ≤ M)
    (hR : 1 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x y : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ R)
    (hy : ∀ i, |y i - x i| ≤ δ) :
    |MvPolynomial.eval y P - MvPolynomial.eval x P| ≤ 216 * M * R ^ 2 * δ := by
  have h := Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_sub_le P hP M hM
    R δ hR hδ0 hδ1 (fun i => (x i : ℂ)) (fun i => (y i : ℂ))
    (fun i => by simpa using hx i) (fun i => by simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hy i)
  rw [Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_ofReal P y, Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_ofReal P x, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
