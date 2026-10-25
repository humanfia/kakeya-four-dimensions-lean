/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.PolynomialTaylor

open MvPolynomial
namespace Submission.Lib.K4CubicTests

/-- The coordinate primitive with zero constant term in that coordinate. -/
noncomputable def polynomialPartialPrimitive {σ : Type*} (i : σ) :
    MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ :=
  (MvPolynomial.basisMonomials σ ℝ).constr ℝ fun m =>
    monomial (m + Finsupp.single i 1) (((m i + 1 : ℕ) : ℝ)⁻¹)

theorem polynomialPartialPrimitive_monomial_one {σ : Type*} (i : σ) (m : σ →₀ ℕ) :
    polynomialPartialPrimitive i (monomial m 1) =
      monomial (m + Finsupp.single i 1) (((m i + 1 : ℕ) : ℝ)⁻¹) := by
  change polynomialPartialPrimitive i ((MvPolynomial.basisMonomials σ ℝ) m) = _
  exact Module.Basis.constr_basis _ _ _ _

theorem pderiv_polynomialPartialPrimitive {σ : Type*} (i : σ) (F : MvPolynomial σ ℝ) :
    pderiv i (polynomialPartialPrimitive i F) = F := by
  classical
  have h : (pderiv i).toLinearMap.comp (polynomialPartialPrimitive i) = LinearMap.id := by
    apply (MvPolynomial.basisMonomials σ ℝ).ext
    intro m
    change pderiv i (polynomialPartialPrimitive i (monomial m 1)) = monomial m 1
    rw [polynomialPartialPrimitive_monomial_one, pderiv_monomial, add_tsub_cancel_right]
    congr 1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
    exact inv_mul_cancel₀ (by positivity)
  exact congrArg (fun f : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ => f F) h


/-- The formal chain rule for polynomial substitutions. -/
theorem pderiv_aeval_polynomial {σ τ : Type*} [Fintype σ]
    (F : MvPolynomial σ ℝ) (g : σ → MvPolynomial τ ℝ) (j : τ) :
    pderiv j (aeval g F) = ∑ i, aeval g (pderiv i F) * pderiv j (g i) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, aeval_X, pderiv_mul, map_add, pderiv_X, hp]
    simp [Pi.single_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum,
      Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

/-- The chosen coordinate primitive vanishes on the zero coordinate hyperplane. -/
theorem eval_polynomialPartialPrimitive_eq_zero {σ : Type*} (i : σ)
    (F : MvPolynomial σ ℝ) (a : σ → ℝ) (ha : a i = 0) :
    MvPolynomial.eval a (polynomialPartialPrimitive i F) = 0 := by
  classical
  have h : (aeval a).toLinearMap.comp (polynomialPartialPrimitive i) = 0 := by
    apply (MvPolynomial.basisMonomials σ ℝ).ext
    intro m
    change MvPolynomial.eval a (polynomialPartialPrimitive i (monomial m 1)) = 0
    rw [polynomialPartialPrimitive_monomial_one, eval_monomial]
    have hi : i ∈ (m + Finsupp.single i 1).support := by simp
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    simp [ha]
  exact congrArg (fun f : MvPolynomial σ ℝ →ₗ[ℝ] ℝ => f F) h


theorem polynomialPartialPrimitive_monomial {σ : Type*} (i : σ) (m : σ →₀ ℕ) (a : ℝ) :
    polynomialPartialPrimitive i (monomial m a) =
      monomial (m + Finsupp.single i 1) (a / ((m i + 1 : ℕ) : ℝ)) := by
  have heq : monomial m a = a • (monomial m 1 : MvPolynomial σ ℝ) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [heq, map_smul, polynomialPartialPrimitive_monomial_one, smul_monomial, smul_eq_mul, div_eq_mul_inv]

theorem polynomialPartialPrimitive_pderiv_comm {σ : Type*} (i j : σ) (hij : i ≠ j)
    (F : MvPolynomial σ ℝ) :
    pderiv j (polynomialPartialPrimitive i F) = polynomialPartialPrimitive i (pderiv j F) := by
  classical
  have h : (pderiv j).toLinearMap.comp (polynomialPartialPrimitive i) =
      (polynomialPartialPrimitive i).comp (pderiv j).toLinearMap := by
    apply (MvPolynomial.basisMonomials σ ℝ).ext
    intro m
    change pderiv j (polynomialPartialPrimitive i (monomial m 1)) =
      polynomialPartialPrimitive i (pderiv j (monomial m 1))
    rw [polynomialPartialPrimitive_monomial_one, pderiv_monomial, pderiv_monomial,
      polynomialPartialPrimitive_monomial]
    have hexp : m + Finsupp.single i 1 - Finsupp.single j 1 =
        (m - Finsupp.single j 1) + Finsupp.single i 1 := by
      ext k
      by_cases hki : k = i
      · subst k; simp [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply, hij]
      · simp [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply, hki]
    rw [hexp]
    congr 1
    simp [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply, hij, Ne.symm hij, div_eq_mul_inv, mul_comm]
  exact congrArg (fun f : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial σ ℝ => f F) h


/-- Add the coordinate integrals of successive leg integrands. -/
noncomputable def polynomialEndpointIntegral {κ : Type*} [Fintype κ]
    (F : κ → MvPolynomial κ ℝ) : MvPolynomial κ ℝ :=
  ∑ k, polynomialPartialPrimitive k (F k)

/-- Only the two legs indexed by the differentiated coordinates contribute
to an off-diagonal endpoint Hessian at zero. -/
theorem polynomialEndpointIntegral_mixedHessian {κ : Type*} [Fintype κ]
    (F : κ → MvPolynomial κ ℝ) (i j : κ) (hij : i ≠ j) :
    MvPolynomial.eval (fun _ => 0) (pderiv i (pderiv j (polynomialEndpointIntegral F))) =
      MvPolynomial.eval (fun _ => 0) (pderiv i (F j)) +
        MvPolynomial.eval (fun _ => 0) (pderiv j (F i)) := by
  classical
  have hterm (k : κ) :
      MvPolynomial.eval (fun _ => 0) (pderiv i (pderiv j (polynomialPartialPrimitive k (F k)))) =
        (if k = j then MvPolynomial.eval (fun _ => 0) (pderiv i (F j))
          else 0) +
        (if k = i then MvPolynomial.eval (fun _ => 0) (pderiv j (F i)) else 0) := by
    by_cases hkj : k = j
    · subst k
      rw [pderiv_polynomialPartialPrimitive]
      simp [Ne.symm hij]
    · by_cases hki : k = i
      · subst k
        rw [polynomialPartialPrimitive_pderiv_comm i j hij, pderiv_polynomialPartialPrimitive]
        simp [hij]
      · rw [polynomialPartialPrimitive_pderiv_comm k j hkj,
          polynomialPartialPrimitive_pderiv_comm k i hki,
          eval_polynomialPartialPrimitive_eq_zero k _ (fun _ => 0) rfl]
        simp [hkj, hki]
  simp only [polynomialEndpointIntegral, map_sum]
  simp_rw [hterm]
  simp [Finset.sum_add_distrib]


/-- Evaluating the coordinate primitive along that coordinate gives an
ordinary one-dimensional antiderivative, with all other coordinates fixed. -/
theorem hasDerivAt_eval_polynomialPartialPrimitive {σ : Type*} [Fintype σ] [DecidableEq σ]
    (i : σ) (F : MvPolynomial σ ℝ) (a : σ → ℝ) (t : ℝ) :
    HasDerivAt (fun x => MvPolynomial.eval (Function.update a i x) (polynomialPartialPrimitive i F))
      (MvPolynomial.eval (Function.update a i t) F) t := by
  classical
  have hz (j : σ) : HasDerivAt (fun x => Function.update a i x j)
      (if j = i then 1 else 0) t := by
    by_cases hji : j = i
    · subst j; convert hasDerivAt_id t using 1 <;> simp <;> rfl
    · simpa [Function.update_of_ne hji, hji] using hasDerivAt_const t (a j)
  have h := hasDerivAt_eval_finite_polynomial_curve (polynomialPartialPrimitive i F)
    (fun x => Function.update a i x) (fun j => if j = i then 1 else 0) t hz
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    pderiv_polynomialPartialPrimitive] using h

/-- The polynomial coordinate primitive represents the actual signed line
integral, including negative leg durations. -/
theorem integral_eval_polynomial_eq_primitive_sub {σ : Type*} [Fintype σ] [DecidableEq σ]
    (i : σ) (F : MvPolynomial σ ℝ) (a : σ → ℝ) (s t : ℝ) :
    (∫ x in s..t, MvPolynomial.eval (Function.update a i x) F) =
      MvPolynomial.eval (Function.update a i t) (polynomialPartialPrimitive i F) -
        MvPolynomial.eval (Function.update a i s) (polynomialPartialPrimitive i F) := by
  have hc : Continuous (fun x => MvPolynomial.eval (Function.update a i x) F) := by
    apply (MvPolynomial.continuous_eval F).comp
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_eval_polynomialPartialPrimitive i F a x) (hc.intervalIntegrable s t)

theorem integral_eval_polynomial_from_zero {σ : Type*} [Fintype σ] [DecidableEq σ]
    (i : σ) (F : MvPolynomial σ ℝ) (a : σ → ℝ) (t : ℝ) :
    (∫ x in (0:ℝ)..t, MvPolynomial.eval (Function.update a i x) F) =
      MvPolynomial.eval (Function.update a i t) (polynomialPartialPrimitive i F) := by
  have hzero : MvPolynomial.eval (Function.update a i 0) (polynomialPartialPrimitive i F) = 0 :=
    eval_polynomialPartialPrimitive_eq_zero i F _ (by simp)
  rw [integral_eval_polynomial_eq_primitive_sub i F a 0 t, hzero, sub_zero]


theorem polynomialPartialPrimitive_totalDegree_le {σ : Type*} (i : σ) (F : MvPolynomial σ ℝ) :
    (polynomialPartialPrimitive i F).totalDegree ≤ F.totalDegree + 1 := by
  classical
  have hs := congrArg (polynomialPartialPrimitive i) (MvPolynomial.as_sum F)
  simp only [map_sum] at hs
  rw [hs]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [polynomialPartialPrimitive_monomial]
  apply (totalDegree_monomial_le _ _).trans
  change Finsupp.degree (m + Finsupp.single i 1) ≤ F.totalDegree + 1
  rw [map_add, Finsupp.degree_single]
  exact Nat.add_le_add_right (le_totalDegree hm) 1

theorem polynomialEndpointIntegral_totalDegree_le {κ : Type*} [Fintype κ]
    (F : κ → MvPolynomial κ ℝ) (D : ℕ) (hD : ∀ k, (F k).totalDegree ≤ D) :
    (polynomialEndpointIntegral F).totalDegree ≤ D + 1 := by
  classical
  apply totalDegree_finsetSum_le
  intro k hk
  exact (polynomialPartialPrimitive_totalDegree_le k (F k)).trans (Nat.add_le_add_right (hD k) 1)

end Submission.Lib.K4CubicTests
