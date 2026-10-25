import Submission.Obl.k4_seven_direction_local_degree_restoration.Taylor
import Submission.Obl.k4_seven_direction_local_degree_restoration.Quadratic
namespace Submission.Obl.k4_seven_direction_local_degree_restoration
noncomputable def bilinearOf (T : Base [×2]→L[ℝ] ℝ) : Base →L[ℝ] Base →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin1 ℝ Base ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp T.curryLeft
lemma bilinearOf_apply (T : Base [×2]→L[ℝ] ℝ) (x y : Base) :
    bilinearOf T x y = T ![x,y] := by
  simp [bilinearOf, ContinuousMultilinearMap.curryLeft_apply]
lemma sum_coordinates (x : Base) : ∑ i : Fin 3, x i • EuclideanSpace.basisFun (Fin 3) ℝ i = x :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
lemma linear_coordinates (L : Base →L[ℝ] ℝ) (x : Base) :
    ∑ i : Fin 3, L (EuclideanSpace.basisFun (Fin 3) ℝ i) * x i = L x := by
  conv_rhs => rw [← sum_coordinates x]
  simp [mul_comm]
lemma bilinear_coordinates (T : Base [×2]→L[ℝ] ℝ) (x y : Base) :
    ∑ i : Fin 3, ∑ j : Fin 3,
      T ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j] * x i * y j =
        T ![x,y] := by
  simp_rw [← bilinearOf_apply]
  conv_rhs => rw [← sum_coordinates x, ← sum_coordinates y]
  simp [map_sum, map_smul, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]


/-- The quadratic Taylor graph test, in the actual four polynomial variables. -/
noncomputable def quadraticTaylorGraph (f : Base → ℝ) : Poly :=
  quadraticGraph (f 0)
    (fun i => fderiv ℝ f 0 (EuclideanSpace.basisFun (Fin 3) ℝ i))
    (fun i j => iteratedFDeriv ℝ 2 f 0
      ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j] / 2)

lemma quadraticTaylorGraph_eval (f : Base → ℝ) (u : Base) (w : ℝ) :
    MvPolynomial.eval ![u 0, u 1, u 2, w] (quadraticTaylorGraph f) =
      w - (f 0 + fderiv ℝ f 0 u + iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2) := by
  rw [quadraticTaylorGraph, quadraticGraph_eval, linear_coordinates]
  congr 2
  have hdiv : (∑ i : Fin 3, ∑ j : Fin 3,
      iteratedFDeriv ℝ 2 f 0
        ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j] / 2 * u i * u j) =
      (∑ i : Fin 3, ∑ j : Fin 3,
      iteratedFDeriv ℝ 2 f 0
        ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j] * u i * u j) / 2 := by
    simp_rw [div_mul_eq_mul_div, Finset.sum_div]
  rw [hdiv, bilinear_coordinates]
  congr 2
  funext i
  fin_cases i <;> rfl

lemma quadraticTaylorGraph_coeff_le {f : Base → ℝ} {Z : ℝ} (hZ : 2 ≤ Z)
    (h0 : |f 0| ≤ Z) (h1 : ‖fderiv ℝ f 0‖ ≤ Z)
    (h2 : ‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z) (e : Fin 4 →₀ ℕ) :
    |(quadraticTaylorGraph f).coeff e| ≤ Z ^ 5 := by
  refine quadraticGraph_coeff_le_pow hZ h0 ?_ ?_ e
  · intro i
    have h := (fderiv ℝ f 0).le_opNorm (EuclideanSpace.basisFun (Fin 3) ℝ i)
    have hi : ‖EuclideanSpace.basisFun (Fin 3) ℝ i‖ = 1 := by
      simp [EuclideanSpace.basisFun_apply]
    simpa [hi, Real.norm_eq_abs] using h.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  · intro i j
    have h := (iteratedFDeriv ℝ 2 f 0).le_opNorm
      ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j]
    have h' : |iteratedFDeriv ℝ 2 f 0
        ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j]| ≤ Z := by
      simpa [Fin.prod_univ_two, EuclideanSpace.basisFun_apply, Real.norm_eq_abs] using h.trans
        (mul_le_mul_of_nonneg_right h2 (by positivity))
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_div_of_nonneg_right h' (by norm_num : (0 : ℝ) ≤ 2)).trans (by linarith)

/-- A graph with controlled third derivative admits a quadratic test with derivative one. -/
theorem quadraticTaylorGraph_bounds {f : Base → ℝ}
    (hf : ContDiffOn ℝ 3 f (Metric.ball (0 : Base) 3)) {Z B d : ℝ}
    (hZ : 2 ≤ Z) (h0 : |f 0| ≤ Z) (h1 : ‖fderiv ℝ f 0‖ ≤ Z)
    (h2 : ‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z)
    (hB : ∀ u ∈ Metric.closedBall (0 : Base) 1, ‖iteratedFDeriv ℝ 3 f u‖ ≤ B) :
    (quadraticTaylorGraph f).totalDegree ≤ 2 ∧
    (∀ e, |(quadraticTaylorGraph f).coeff e| ≤ Z ^ 5) ∧
    MvPolynomial.pderiv (3 : Fin 4) (quadraticTaylorGraph f) = 1 ∧
    ∀ u ∈ Metric.closedBall (0 : Base) 1, ∀ w : ℝ, |w - f u| ≤ d →
      |MvPolynomial.eval ![u 0, u 1, u 2, w] (quadraticTaylorGraph f)| ≤ d + B / 6 := by
  refine ⟨quadraticGraph_totalDegree _ _ _, quadraticTaylorGraph_coeff_le hZ h0 h1 h2,
    quadraticGraph_pderiv _ _ _, ?_⟩
  intro u hu w hw
  rw [quadraticTaylorGraph_eval]
  have h := abs_sub_quadratic_taylor_le hf hB hu
  calc
    |w - (f 0 + fderiv ℝ f 0 u + iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2)| ≤
        |w - f u| + |f u - (f 0 + fderiv ℝ f 0 u + iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2)| :=
      abs_sub_le _ _ _
    _ ≤ d + B / 6 := add_le_add hw h

end Submission.Obl.k4_seven_direction_local_degree_restoration
