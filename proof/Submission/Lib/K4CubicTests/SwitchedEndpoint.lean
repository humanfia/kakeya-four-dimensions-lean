/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.PolynomialIntegrals

open MvPolynomial

namespace Submission.Lib.K4CubicTests

/-- The polynomial base position at the end of the current leg. -/
noncomputable def switchedBasePrefix {σ κ : Type*} [Fintype κ] [LinearOrder κ]
    (c : σ → ℝ) (v : κ → σ → ℝ) (k : κ) (a : σ) : MvPolynomial κ ℝ :=
  C (c a) + ∑ l : κ, if l ≤ k then C (v l a) * X l else 0

/-- The field contracted against the current direction, as a polynomial in
all leg durations. The prefix contains no later durations. -/
noncomputable def switchedLegIntegrand {σ κ : Type*} [Fintype σ] [Fintype κ] [LinearOrder κ]
    (T : σ → MvPolynomial σ ℝ) (c : σ → ℝ) (v : κ → σ → ℝ) (k : κ) : MvPolynomial κ ℝ :=
  ∑ a, C (v k a) * aeval (switchedBasePrefix c v k) (T a)

/-- The accumulated height of the successive polynomial field integrals. -/
noncomputable def switchedEndpointHeight {σ κ : Type*} [Fintype σ] [Fintype κ] [LinearOrder κ]
    (T : σ → MvPolynomial σ ℝ) (c : σ → ℝ) (v : κ → σ → ℝ) : MvPolynomial κ ℝ :=
  polynomialEndpointIntegral (switchedLegIntegrand T c v)

theorem eval_switchedBasePrefix_zero {σ κ : Type*} [Fintype κ] [LinearOrder κ]
    (c : σ → ℝ) (v : κ → σ → ℝ) (k : κ) (a : σ) :
    MvPolynomial.eval (fun _ => 0) (switchedBasePrefix c v k a) = c a := by
  classical
  simp [switchedBasePrefix, apply_ite]

theorem pderiv_switchedBasePrefix {σ κ : Type*} [Fintype κ] [LinearOrder κ]
    (c : σ → ℝ) (v : κ → σ → ℝ) (k j : κ) (a : σ) :
    pderiv j (switchedBasePrefix c v k a) = if j ≤ k then C (v j a) else 0 := by
  classical
  simp only [switchedBasePrefix, map_add, pderiv_C, zero_add, map_sum, apply_ite,
    pderiv_C_mul, pderiv_X, map_zero]
  have ht (l : κ) : (if l ≤ k then C (v l a) * Pi.single (M := fun _ : κ => MvPolynomial κ ℝ) j 1 l else 0) =
      if l = j then (if j ≤ k then C (v j a) else 0) else 0 := by
    by_cases hlj : l = j
    · subst l; simp
    · simp [Pi.single_apply, hlj, Ne.symm hlj]
  simp_rw [ht]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hjk : j ≤ k <;> simp [hjk]

theorem eval_pderiv_switchedLegIntegrand_zero {σ κ : Type*}
    [Fintype σ] [Fintype κ] [LinearOrder κ]
    (T : σ → MvPolynomial σ ℝ) (c : σ → ℝ) (v : κ → σ → ℝ) (k j : κ) :
    MvPolynomial.eval (fun _ => 0) (pderiv j (switchedLegIntegrand T c v k)) =
      if j ≤ k then ∑ a, ∑ b, v k a * MvPolynomial.eval c (pderiv b (T a)) * v j b else 0 := by
  classical
  have heval (P : MvPolynomial σ ℝ) :
      MvPolynomial.eval (fun _ => 0) (aeval (switchedBasePrefix c v k) P) = MvPolynomial.eval c P := by
    change (aeval (fun _ : κ => (0:ℝ))) (aeval (switchedBasePrefix c v k) P) = _
    rw [comp_aeval_apply]
    simp only [aeval_eq_eval, eval_switchedBasePrefix_zero]
  simp only [switchedLegIntegrand, map_sum, pderiv_C_mul, pderiv_aeval_polynomial,
    pderiv_switchedBasePrefix, map_mul, eval_C, heval]
  by_cases hjk : j ≤ k
  · simp [hjk, Finset.mul_sum, mul_assoc]
  · simp [hjk]

/-- The exact mixed-Hessian identity of the simulated endpoint. A duration
from an earlier leg differentiates the field at the start of the later leg. -/
theorem switchedEndpointHeight_mixedHessian {σ κ : Type*}
    [Fintype σ] [Fintype κ] [LinearOrder κ]
    (T : σ → MvPolynomial σ ℝ) (c : σ → ℝ) (v : κ → σ → ℝ)
    (i j : κ) (hij : i < j) :
    MvPolynomial.eval (fun _ => 0) (pderiv i (pderiv j (switchedEndpointHeight T c v))) =
      ∑ a, ∑ b, v j a * MvPolynomial.eval c (pderiv b (T a)) * v i b := by
  rw [switchedEndpointHeight, polynomialEndpointIntegral_mixedHessian _ i j (ne_of_lt hij),
    eval_pderiv_switchedLegIntegrand_zero, eval_pderiv_switchedLegIntegrand_zero]
  simp only [le_of_lt hij, ite_true, not_le.mpr hij, ite_false, add_zero]


/-- Evaluation of the affine prefix in actual duration coordinates. -/
theorem eval_switchedBasePrefix {σ κ : Type*} [Fintype κ] [LinearOrder κ]
    (c : σ → ℝ) (v : κ → σ → ℝ) (k : κ) (a : σ) (δ : κ → ℝ) :
    MvPolynomial.eval δ (switchedBasePrefix c v k a) =
      c a + ∑ l : κ, if l ≤ k then v l a * δ l else 0 := by
  classical
  simp only [switchedBasePrefix, map_add, map_sum, apply_ite, map_mul, eval_C, eval_X, map_zero]

/-- Evaluation of one leg's polynomial gives the field along its base line. -/
theorem eval_switchedLegIntegrand {σ κ : Type*}
    [Fintype σ] [Fintype κ] [LinearOrder κ]
    (T : σ → MvPolynomial σ ℝ) (c : σ → ℝ) (v : κ → σ → ℝ) (k : κ) (δ : κ → ℝ) :
    MvPolynomial.eval δ (switchedLegIntegrand T c v k) =
      ∑ a, v k a * MvPolynomial.eval
        (fun b => c b + ∑ l : κ, if l ≤ k then v l b * δ l else 0) (T a) := by
  classical
  simp only [switchedLegIntegrand, map_sum, map_mul, eval_C]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  change (aeval δ) (aeval (switchedBasePrefix c v k) (T a)) = _
  rw [comp_aeval_apply]
  simp only [aeval_eq_eval, eval_switchedBasePrefix]

/-- The endpoint polynomial is the sum of the actual signed field integrals
along its successive affine legs. -/
theorem eval_switchedEndpointHeight_eq_integral {σ κ : Type*}
    [Fintype σ] [Fintype κ] [LinearOrder κ]
    (T : σ → MvPolynomial σ ℝ) (c : σ → ℝ) (v : κ → σ → ℝ) (δ : κ → ℝ) :
    MvPolynomial.eval δ (switchedEndpointHeight T c v) =
      ∑ k : κ, ∫ s in (0:ℝ)..δ k, ∑ a, v k a * MvPolynomial.eval
        (fun b => c b + ∑ l : κ, if l ≤ k then v l b * Function.update δ k s l else 0) (T a) := by
  classical
  simp only [switchedEndpointHeight, polynomialEndpointIntegral, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h := integral_eval_polynomial_from_zero k (switchedLegIntegrand T c v k) δ (δ k)
  have hu : Function.update δ k (δ k) = δ := by ext j; by_cases hj : j = k <;> simp [hj]
  rw [hu] at h
  refine h.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro s hs
  exact eval_switchedLegIntegrand T c v k (Function.update δ k s)

end Submission.Lib.K4CubicTests
