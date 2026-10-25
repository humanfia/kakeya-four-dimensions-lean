import Submission.Obl.k4_scalar_tangent_isotropic_improvement.Restoration
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.PolynomialComparison

/-! Formal third directional derivatives of polynomial potentials along affine base trajectories. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open MvPolynomial

/-- Substitute an affine line with base velocity `(1,v)`. -/
def affineLineHom (a : Fin 2 → ℝ) (v : ℝ) : MvPolynomial (Fin 2) ℝ →+* Polynomial ℝ :=
  eval₂Hom Polynomial.C
    ![Polynomial.C (a 0) + Polynomial.X, Polynomial.C (a 1) + Polynomial.C v * Polynomial.X]

/-- The formal directional derivative in `(1,v)`. -/
def directionalPolynomial (p : MvPolynomial (Fin 2) ℝ) (v : ℝ) : MvPolynomial (Fin 2) ℝ :=
  pderiv 0 p + C v * pderiv 1 p

theorem eval_affineLineHom (p : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (v t : ℝ) :
    (affineLineHom a v p).eval t = eval ![a 0 + t, a 1 + v * t] p := by
  rw [affineLineHom, coe_eval₂Hom,
    Submission.Obl.k4_quadratic_slope_volume.eval_polynomial_substitution]
  apply congrArg (fun x : Fin 2 → ℝ => eval x p)
  ext i
  fin_cases i <;> simp

theorem natDegree_affineLineHom_le (p : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (v : ℝ) :
    (affineLineHom a v p).natDegree ≤ p.totalDegree := by
  apply Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le
  intro i
  fin_cases i <;> simp
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

theorem derivative_affineLineHom (p : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (v : ℝ) :
    (affineLineHom a v p).derivative = affineLineHom a v (directionalPolynomial p v) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [affineLineHom, directionalPolynomial]
  | add p q hp hq =>
    simp only [map_add, Polynomial.derivative_add, hp, hq]
    simp [directionalPolynomial, map_add]
    ring
  | mul_X p i hp =>
    fin_cases i <;>
      simp [affineLineHom, directionalPolynomial, Polynomial.derivative_mul, pderiv_mul,
        pderiv_X, Pi.single_apply] at hp ⊢ <;> rw [hp] <;> ring

theorem pderiv_one_zero_commute (p : MvPolynomial (Fin 2) ℝ) :
    pderiv 1 (pderiv 0 p) = pderiv 0 (pderiv 1 p) := by
  ext d
  simp only [coeff_pderiv]
  rw [show d + Finsupp.single 1 1 + Finsupp.single 0 1 =
      d + Finsupp.single 0 1 + Finsupp.single 1 1 by abel]
  simp
  ring

/-- The cubic test polynomial is the third formal directional derivative. -/
theorem directionalPolynomial_three (p : MvPolynomial (Fin 2) ℝ) (v : ℝ) :
    directionalPolynomial (directionalPolynomial (directionalPolynomial p v) v) v =
      cubicPolynomial p v := by
  simp only [directionalPolynomial, map_add, pderiv_C_mul]
  simp_rw [pderiv_one_zero_commute]
  simp [cubicPolynomial, thirdPartials, Fin.sum_univ_succ, Algebra.smul_def]
  ring

/-- Three ordinary derivatives of a line restriction are its cubic direction
polynomial restricted to the same affine line. -/
theorem third_derivative_affineLineHom (p : MvPolynomial (Fin 2) ℝ)
    (a : Fin 2 → ℝ) (v : ℝ) :
    (Polynomial.derivative^[3]) (affineLineHom a v p) = affineLineHom a v (cubicPolynomial p v) := by
  change ((affineLineHom a v p).derivative.derivative).derivative = _
  rw [derivative_affineLineHom, derivative_affineLineHom, derivative_affineLineHom,
    directionalPolynomial_three]

/-- The value of the third derivative is the scalar cubic test at the actual
trajectory point. -/
theorem eval_third_derivative_affineLineHom (p : MvPolynomial (Fin 2) ℝ)
    (a : Fin 2 → ℝ) (v t : ℝ) :
    ((Polynomial.derivative^[3]) (affineLineHom a v p)).eval t =
      cubicTest p ![a 0 + t, a 1 + v * t] v := by
  rw [third_derivative_affineLineHom, eval_affineLineHom, eval_cubicPolynomial]

/-- A whole-block fit to a quadratic trajectory bounds the third directional
test on that entire normalized block. -/
theorem exists_cubicTest_bound_of_line_fit (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (v : ℝ) (f : Polynomial ℝ) (E : ℝ),
      p.totalDegree ≤ D → f.natDegree ≤ 2 → 0 ≤ E →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, |f.eval t - eval ![a 0 + t, a 1 + v * t] p| ≤ E) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, |cubicTest p ![a 0 + t, a 1 + v * t] v| ≤ C * E := by
  obtain ⟨C, hC, hderiv⟩ := exists_polynomial_iterated_derivative_bound (D + 2) 3
  refine ⟨C, hC, ?_⟩
  intro p a v f E hp hf hE hfit
  let g : Polynomial ℝ := affineLineHom a v p - f
  have hg : g.natDegree ≤ D + 2 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le ((natDegree_affineLineHom_le p a v).trans (hp.trans (by omega))) (hf.trans (by omega)))
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g.eval t| ≤ E := by
    intro t ht
    simpa only [g, Polynomial.eval_sub, eval_affineLineHom, abs_sub_comm] using hfit t ht
  have hzero : (Polynomial.derivative^[3]) f = 0 := Polynomial.iterate_derivative_eq_zero (by omega)
  have hthird : (Polynomial.derivative^[3]) g = affineLineHom a v (cubicPolynomial p v) := by
    dsimp only [g]
    rw [Polynomial.iterate_derivative_sub, hzero, sub_zero, third_derivative_affineLineHom]
  intro t ht
  have h := hderiv g E hg hE hbound t ht
  rwa [hthird, eval_affineLineHom, eval_cubicPolynomial] at h

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
