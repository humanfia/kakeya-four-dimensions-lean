import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticPolynomial
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Grouping

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MvPolynomial Set

/-- The six standard monomials of a bivariate quadratic are distinct. -/
theorem quadraticExponent_injective : Function.Injective quadraticExponent := by
  intro i j hij
  have h₀ := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hij
  have h₁ := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hij
  fin_cases i <;> fin_cases j <;> norm_num [quadraticExponent] at *

theorem coeff_quadraticPolynomial (c : Fin 6 → ℝ) (i : Fin 6) :
    (quadraticPolynomial c).coeff (quadraticExponent i) = c i := by
  simp [quadraticPolynomial, coeff_sum, coeff_monomial, quadraticExponent_injective.eq_iff]

/-- Every degree-two predictor has its ordinary six coefficients bounded by the
same bound on its multivariate polynomial coefficients. -/
theorem exists_quadratic_coefficients {P : MvPolynomial (Fin 2) ℝ} {H : ℝ}
    (hP : P.totalDegree ≤ 2) (hcoeff : ∀ e, |P.coeff e| ≤ H) :
    ∃ c : Fin 6 → ℝ,
      (∀ t y, MvPolynomial.eval ![t, y] P = quadraticValue c t y) ∧
      (∀ i, |c i| ≤ H) := by
  obtain ⟨c, hc⟩ := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.isQuad2_eval P hP
  have hPc := polynomial_eq_of_quadratic_values hc
  refine ⟨c, hc, fun i => ?_⟩
  simpa only [hPc, coeff_quadraticPolynomial] using hcoeff (quadraticExponent i)

/-- On a clipped scalar trajectory, the observed coordinate is at most twice the
coefficient bound throughout the unit time interval. -/
theorem scalarY_bound_of_box {R : ℝ} {z : Fin 5 → ℝ} (hz : z ∈ coefficientBox R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |scalarY z t| ≤ 2 * R := by
  have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  calc
    _ ≤ |z 0| + |t * z 1| := abs_add_le _ _
    _ ≤ R + 1 * R := by rw [abs_mul]; gcongr; exact hz 0; exact hz 1
    _ = _ := by ring

/-- Perturbing every quadratic coefficient by `ρ` costs at most `24 ρ R²` on
a scalar fit clipped to the coefficient box of radius `R`. -/
theorem clipped_fit_perturbation
    {P : MvPolynomial (Fin 2) ℝ} {c c' : Fin 6 → ℝ} {R ρ error : ℝ}
    (hR : 1 ≤ R) (hρ : 0 ≤ ρ)
    (hc : ∀ t y, MvPolynomial.eval ![t, y] P = quadraticValue c t y)
    (hdiff : ∀ i, |c i - c' i| ≤ ρ)
    {z : Fin 5 → ℝ} (hz : z ∈ coefficientBox R)
    (hfit : z ∈ scalarFit P error) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |scalarX z t - MvPolynomial.eval ![t, scalarY z t] (quadraticPolynomial c')| ≤
      error + 24 * ρ * R ^ 2 := by
  have ht' : |t| ≤ 2 * R := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
  have hy : |scalarY z t| ≤ 2 * R := scalarY_bound_of_box hz ht
  have hp := quadraticValue_sub_bound hρ (by linarith : 1 ≤ 2 * R) hdiff ht' hy
  rw [eval_quadraticPolynomial]
  calc
    _ ≤ |scalarX z t - quadraticValue c t (scalarY z t)| +
        |quadraticValue c t (scalarY z t) - quadraticValue c' t (scalarY z t)| :=
      abs_sub_le _ _ _
    _ ≤ error + 6 * ρ * (2 * R) ^ 2 := by
      apply add_le_add _ hp
      rw [← hc]
      exact hfit t ht
    _ = _ := by ring

end Submission.Obl.k4_fixed_budget_quadratic_recovery
