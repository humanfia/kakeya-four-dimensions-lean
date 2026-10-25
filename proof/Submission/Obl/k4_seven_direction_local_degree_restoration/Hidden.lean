import Submission.Obl.k4_seven_direction_local_degree_restoration.Quadratic
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices
import Submission.Obl.k4_prescribed_polynomial_visibility.PolynomialSmooth

namespace Submission.Obl.k4_seven_direction_local_degree_restoration

noncomputable def evalAt (P : Poly) (u : Base) (w : ℝ) : ℝ :=
  MvPolynomial.eval ![u 0, u 1, u 2, w] P

noncomputable def hiddenPolynomial (P : Poly) (u : Base) : Polynomial ℝ :=
  Submission.Obl.k4_quadratic_slope_volume.coordinatePolynomialHom
    ![u 0, u 1, u 2, 0] (3 : Fin 4) P

lemma hiddenPolynomial_eval (P : Poly) (u : Base) (w : ℝ) :
    (hiddenPolynomial P u).eval w = evalAt P u w := by
  rw [hiddenPolynomial, Submission.Obl.k4_quadratic_slope_volume.eval_coordinatePolynomialHom]
  apply congrArg (fun x : Fin 4 → ℝ => MvPolynomial.eval x P)
  funext i
  fin_cases i <;> simp

lemma hiddenPolynomial_derivative (P : Poly) (u : Base) :
    (hiddenPolynomial P u).derivative = hiddenPolynomial (MvPolynomial.pderiv (3 : Fin 4) P) u :=
  Submission.Obl.k4_quadratic_slope_volume.derivative_coordinatePolynomialHom P _ _

lemma hiddenPolynomial_natDegree (P : Poly) (u : Base) :
    (hiddenPolynomial P u).natDegree ≤ P.totalDegree := by
  apply Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le
  intro i
  split_ifs <;> simp

/-- The exact quadratic Taylor identity, based at the right endpoint. -/
lemma quadratic_taylor_at_right (P : Polynomial ℝ) (hP : P.natDegree ≤ 2) (x y : ℝ) :
    P.eval y - P.eval x = P.derivative.eval y * (y - x) -
      P.derivative.derivative.eval y / 2 * (y - x) ^ 2 := by
  obtain ⟨a, b, c, rfl⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients P hP
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.eval_zero, Polynomial.eval_one]
  norm_num
  ring

lemma hidden_quadratic_taylor (P : Poly) (hP : P.totalDegree ≤ 2) (u : Base) (v w : ℝ) :
    evalAt P u w - evalAt P u v =
      evalAt (MvPolynomial.pderiv (3 : Fin 4) P) u w * (w - v) -
        evalAt (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P)) u w / 2 *
          (w - v) ^ 2 := by
  have h := quadratic_taylor_at_right (hiddenPolynomial P u)
    ((hiddenPolynomial_natDegree P u).trans hP) v w
  simpa only [hiddenPolynomial_derivative, hiddenPolynomial_eval] using h

lemma abs_hidden_quadratic_sub_le (P : Poly) (hP : P.totalDegree ≤ 2) (u : Base)
    {v w d M B : ℝ} (hd : |w - v| ≤ d)
    (hM : |evalAt (MvPolynomial.pderiv (3 : Fin 4) P) u w| ≤ M)
    (hB : |evalAt (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P)) u w| ≤ B) :
    |evalAt P u w - evalAt P u v| ≤ M * d + B * d ^ 2 / 2 := by
  rw [hidden_quadratic_taylor P hP]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_div, abs_pow]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hd0 := (abs_nonneg (w - v)).trans hd
  have hM0 := (abs_nonneg _).trans hM
  have hB0 := (abs_nonneg _).trans hB
  calc
    |evalAt (MvPolynomial.pderiv (3 : Fin 4) P) u w| * |w - v| +
        |evalAt (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) P)) u w| / 2 *
          |w - v| ^ 2 ≤ M * d + B / 2 * d ^ 2 := by gcongr
    _ = M * d + B * d ^ 2 / 2 := by ring

lemma normalizedGraph_contDiffOn {f : Base → ℝ} {U : Set Base} {n : WithTop ℕ∞}
    (hf : ContDiffOn ℝ n f U) (S : Poly) (a : ℝ) :
    ContDiffOn ℝ n (fun u => evalAt S u (f u) / a) U := by
  have hcoords : ContDiffOn ℝ n (fun u : Base => (![u 0, u 1, u 2, f u] : Fin 4 → ℝ)) U := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (0 : Fin 3) : Base →L[ℝ] ℝ).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (1 : Fin 3) : Base →L[ℝ] ℝ).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (2 : Fin 3) : Base →L[ℝ] ℝ).contDiff.contDiffOn
    · exact hf
  have hgraph : ContDiffOn ℝ n
      (fun u : Base => (WithLp.toLp 2 ![u 0, u 1, u 2, f u] : EuclideanSpace ℝ (Fin 4))) U :=
    PiLp.contDiff_toLp.comp_contDiffOn hcoords
  have hS := Submission.Obl.k4_prescribed_polynomial_visibility.contDiff_polynomial_eval S n
  exact (hS.comp_contDiffOn hgraph).div_const a

end Submission.Obl.k4_seven_direction_local_degree_restoration
