import Submission.Obl.k4_scalar_true_terminal_lifting.CoefficientComposition
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Coefficients

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MvPolynomial
open Submission.Obl.k4_scalar_true_terminal_lifting

/-- Freeze the initial first coordinate to a fine intercept representative,
then return the scalar parameter predictor to the physical `(t,Y)` plane. -/
noncomputable def physicalPredictor (P : MvPolynomial (Fin 2) ℝ)
    (pc qc pa D : ℝ) : MvPolynomial (Fin 2) ℝ :=
  composedPotential 0 P 0 1 qc (pa - 2 * pc) D 1

theorem physicalPredictor_eval (P : MvPolynomial (Fin 2) ℝ)
    (pc qc pa D t Y : ℝ) :
    eval ![t, Y] (physicalPredictor P pc qc pa D) =
      eval ![t, (Y - qc + t * (2 * pc - pa)) / D] P := by
  rw [physicalPredictor, composedPotential_eval]
  simp only [map_zero, zero_add, one_mul, sub_zero, div_one]
  have heq : (Y - qc - t * (pa - 2 * pc)) / D =
      (Y - qc + t * (2 * pc - pa)) / D := by ring
  rw [heq]

theorem physicalPredictor_degree {P : MvPolynomial (Fin 2) ℝ}
    (hP : P.totalDegree ≤ 2) (pc qc pa D : ℝ) :
    (physicalPredictor P pc qc pa D).totalDegree ≤ 2 :=
  composedPotential_degree (by simp) hP _ _ _ _ _ _

/-- Its coefficients depend on the coarse physical width, not the inverse
fine intercept mesh. -/
theorem physicalPredictor_coeff {P : MvPolynomial (Fin 2) ℝ}
    (hP : P.totalDegree ≤ 2) {B H pc qc pa D : ℝ} (_hB : 0 ≤ B)
    (hcoeff : ∀ e, |P.coeff e| ≤ B) (hH : 1 ≤ H) (hD : 0 < D) (hD₁ : D ≤ 1)
    (hpc : |pc| ≤ H) (hqc : |qc| ≤ H) (hpa : |pa| ≤ H) (e : Fin 2 →₀ ℕ) :
    |(physicalPredictor P pc qc pa D).coeff e| ≤ 9 * B * ((1 + 4 * H) / D) ^ 2 := by
  let J := (1 + 4 * H) / D
  have hJ : 1 ≤ J := (le_div_iff₀ hD).mpr (by linarith)
  have htime : |(1 : ℝ)⁻¹| * (1 + |(0 : ℝ)|) ≤ J := by simpa using hJ
  have hspace : |D⁻¹| * (1 + |qc| + |pa - 2 * pc|) ≤ J := by
    rw [abs_inv, abs_of_pos hD, ← div_eq_inv_mul]
    apply div_le_div_of_nonneg_right _ hD.le
    have hsub : |pa - 2 * pc| ≤ |pa| + 2 * |pc| := by
      simpa only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using abs_sub pa (2 * pc)
    linarith
  have hc := composedPotential_coeff (P₀ := 0) (P₁ := P) (B₀ := 0) (B₁ := B)
    (by simp) hP (by simp) hcoeff 0 1 qc (pa - 2 * pc) D 1 J hJ htime hspace e
  simpa only [physicalPredictor, mul_zero, zero_mul, abs_one, one_mul, zero_add, J] using hc

/-- On a bounded comparison domain a quadratic has a controlled change in
its second coordinate. -/
theorem quadratic_second_coordinate_lipschitz {P : MvPolynomial (Fin 2) ℝ}
    (hP : P.totalDegree ≤ 2) {B R t r r' : ℝ} (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hcoeff : ∀ e, |P.coeff e| ≤ B) (ht : |t| ≤ R) (hr : |r| ≤ R) (hr' : |r'| ≤ R) :
    |eval ![t, r] P - eval ![t, r'] P| ≤ 4 * B * R * |r - r'| := by
  obtain ⟨c, hc, hcb⟩ :=
    Submission.Obl.k4_fixed_budget_quadratic_recovery.exists_quadratic_coefficients hP hcoeff
  rw [hc, hc]
  have heq : Submission.Obl.k4_fixed_budget_quadratic_recovery.quadraticValue c t r -
      Submission.Obl.k4_fixed_budget_quadratic_recovery.quadraticValue c t r' =
      (r - r') * (c 2 + c 4 * t + c 5 * (r + r')) := by
    unfold Submission.Obl.k4_fixed_budget_quadratic_recovery.quadraticValue
    ring
  rw [heq, abs_mul, mul_comm |r - r'|]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  calc
    _ ≤ |c 2| + |c 4 * t| + |c 5 * (r + r')| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ B + B * R + B * (R + R) := by
      simp only [abs_mul]
      gcongr
      · exact hcb 2
      · exact hcb 4
      · exact hcb 5
      · exact (abs_add_le _ _).trans (add_le_add hr hr')
    _ ≤ 4 * B * R := by nlinarith

/-- A bounded normalized parameter domain gives a bounded physical moving
interval after freezing the intercept. -/
theorem physicalPredictor_moving_norm {P : MvPolynomial (Fin 2) ℝ}
    (hP : P.totalDegree ≤ 2) {B D pc qc pa : ℝ} (hB : 0 ≤ B) (hD : 0 < D)
    (hcoeff : ∀ e, |P.coeff e| ≤ B) (hcenter : |pc - pa| ≤ 2 * D)
    {t w : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (-1 : ℝ) 1) :
    |eval ![t, qc - t * pa + D * w] (physicalPredictor P pc qc pa D)| ≤ 150 * B := by
  rw [physicalPredictor_eval]
  have ht₁ : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hw₁ : |w| ≤ 1 := abs_le.mpr hw
  have hr : |(qc - t * pa + D * w - qc + t * (2 * pc - pa)) / D| ≤ 5 := by
    have heq : (qc - t * pa + D * w - qc + t * (2 * pc - pa)) / D =
        w + 2 * t * ((pc - pa) / D) := by field_simp; ring
    rw [heq]
    have hratio : |(pc - pa) / D| ≤ 2 := by
      rw [abs_div, abs_of_pos hD]
      exact (div_le_iff₀ hD).mpr hcenter
    calc
      _ ≤ |w| + |2 * t * ((pc - pa) / D)| := abs_add_le _ _
      _ ≤ 1 + 2 * 1 * 2 := by
        have hprod := mul_le_mul ht₁ hratio (abs_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)
        rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        nlinarith
      _ = 5 := by norm_num
  obtain ⟨c, hc, hcb⟩ :=
    Submission.Obl.k4_fixed_budget_quadratic_recovery.exists_quadratic_coefficients hP hcoeff
  rw [hc]
  have hb := Submission.Obl.k4_fixed_budget_quadratic_recovery.quadraticValue_bound
    hB (show (1 : ℝ) ≤ 5 by norm_num) hcb (ht₁.trans (by norm_num)) hr
  convert hb using 1
  ring

/-- Contact and intercept rounding perturb the normalized scalar parameter
only by their physical errors divided by the coarse width. -/
theorem returned_parameter_error {D E χ pc qc pa t p q slope : ℝ}
    (hD : 0 < D) (ht : |t| ≤ 1) (hcontact : |slope + p| ≤ E)
    (hintercept : |p - pa| ≤ χ) :
    |(q + t * slope - qc + t * (2 * pc - pa)) / D -
      ((q - qc) / D - 2 * t * ((p - pc) / D))| ≤ (E + χ) / D := by
  have heq : (q + t * slope - qc + t * (2 * pc - pa)) / D -
      ((q - qc) / D - 2 * t * ((p - pc) / D)) =
      t * ((slope + p) + (p - pa)) / D := by ring
  rw [heq, abs_div, abs_of_pos hD, abs_mul]
  apply div_le_div_of_nonneg_right _ hD.le
  calc
    _ ≤ 1 * (E + χ) := mul_le_mul ht
      ((abs_add_le _ _).trans (add_le_add hcontact hintercept)) (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The full-time scalar fit returns to the physical coordinates with an
explicit error cost; later restrictions do not enter this statement. -/
theorem physicalPredictor_fit {P : MvPolynomial (Fin 2) ℝ}
    (hP : P.totalDegree ≤ 2) {B R D E χ pc qc pa t p q slope X error : ℝ}
    (hB : 0 ≤ B) (hR : 1 ≤ R) (hD : 0 < D)
    (hcoeff : ∀ e, |P.coeff e| ≤ B) (ht : |t| ≤ 1)
    (hcontact : |slope + p| ≤ E) (hintercept : |p - pa| ≤ χ)
    (hr : |(q - qc) / D - 2 * t * ((p - pc) / D)| ≤ R)
    (hr' : |(q + t * slope - qc + t * (2 * pc - pa)) / D| ≤ R)
    (hfit : |X - eval ![t, (q - qc) / D - 2 * t * ((p - pc) / D)] P| ≤ error) :
    |X - eval ![t, q + t * slope] (physicalPredictor P pc qc pa D)| ≤
      error + 4 * B * R * ((E + χ) / D) := by
  rw [physicalPredictor_eval]
  apply (abs_sub_le X (eval ![t, (q - qc) / D - 2 * t * ((p - pc) / D)] P) _).trans
  apply add_le_add hfit
  apply (quadratic_second_coordinate_lipschitz hP hB hR hcoeff (ht.trans hR) hr hr').trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [abs_sub_comm]
  exact returned_parameter_error hD ht hcontact hintercept

end Submission.Obl.k4_horizontal_supercritical_three_projections
