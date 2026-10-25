import Submission.Obl.k4_prescribed_polynomial_visibility.PolynomialSmooth

namespace Submission.Obl.k4_prescribed_polynomial_visibility

/-- Add a new polynomial and split the probability weight equally with the old ensemble. -/
def mixPolynomials {n r : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (p : Fin r → MvPolynomial (Fin n) ℝ) : Fin (r + 1) → MvPolynomial (Fin n) ℝ :=
  Fin.cons P p

noncomputable def mixWeights {r : ℕ} (w : Fin r → ℝ) : Fin (r + 1) → ℝ :=
  Fin.cons (1 / 2) (fun h => w h / 2)

theorem mixWeights_nonneg {r : ℕ} (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h) :
    ∀ h, 0 ≤ mixWeights w h := by
  intro h
  refine Fin.cases ?_ (fun i => ?_) h
  · norm_num [mixWeights]
  · simpa [mixWeights] using div_nonneg (hw i) (by norm_num : (0 : ℝ) ≤ 2)

theorem sum_mixWeights {r : ℕ} (w : Fin r → ℝ) (hw : ∑ h, w h = 1) :
    ∑ h, mixWeights w h = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [mixWeights, Fin.cons_zero, Fin.cons_succ]
  rw [← Finset.sum_div, hw]
  norm_num

theorem mixPolynomials_degree_le {n r : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (p : Fin r → MvPolynomial (Fin n) ℝ) (d : ℝ)
    (hP : (P.totalDegree : ℝ) ≤ d) (hp : ∀ h, ((p h).totalDegree : ℝ) ≤ d) :
    ∀ h, ((mixPolynomials P p h).totalDegree : ℝ) ≤ d := by
  intro h
  refine Fin.cases ?_ (fun i => ?_) h
  · simpa [mixPolynomials] using hP
  · simpa [mixPolynomials] using hp i

/-- The averaged ensemble's exact relation to the previous cost. -/
theorem two_mul_mixed_ensemble {n r : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (p : Fin r → MvPolynomial (Fin n) ℝ) (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h)
    (c v : EuclideanSpace ℝ (Fin n)) :
    2 * ensemble (mixPolynomials P p) (mixWeights w) (mixWeights_nonneg w hw) c v =
      ensemble p w hw c v + polynomialVariation P c v + ‖v‖ := by
  simp only [ensemble_apply, mixPolynomials, mixWeights, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  ring

theorem le_two_mul_mixed_ensemble {n r : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (p : Fin r → MvPolynomial (Fin n) ℝ) (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h)
    (c v : EuclideanSpace ℝ (Fin n)) :
    ensemble p w hw c v + polynomialVariation P c v ≤
      2 * ensemble (mixPolynomials P p) (mixWeights w) (mixWeights_nonneg w hw) c v := by
  rw [two_mul_mixed_ensemble]
  exact le_add_of_nonneg_right (norm_nonneg v)

theorem old_le_two_mul_mixed_ensemble {n r : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (p : Fin r → MvPolynomial (Fin n) ℝ) (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h)
    (c v : EuclideanSpace ℝ (Fin n)) :
    ensemble p w hw c v ≤
      2 * ensemble (mixPolynomials P p) (mixWeights w) (mixWeights_nonneg w hw) c v :=
  (le_add_of_nonneg_right (polynomialVariation_nonneg P c v)).trans
    (le_two_mul_mixed_ensemble P p w hw c v)

end Submission.Obl.k4_prescribed_polynomial_visibility
