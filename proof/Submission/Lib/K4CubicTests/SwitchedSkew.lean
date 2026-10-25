/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.EndpointSkew
import Submission.Lib.K4CubicTests.SwitchedEndpoint

open MvPolynomial

namespace Submission.Lib.K4CubicTests

noncomputable def twoBasisEndpointHeight {m : ℕ}
    (T : Fin m → MvPolynomial (Fin m) ℝ) (c : Fin m → ℝ)
    (A B : Matrix (Fin m) (Fin m) ℝ) : MvPolynomial (Fin (m + m)) ℝ :=
  switchedEndpointHeight T c (Fin.append (fun i a => A a i) (fun i a => B a i))

noncomputable def polynomialFieldDerivative {m : ℕ}
    (T : Fin m → MvPolynomial (Fin m) ℝ) (c : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun a b => MvPolynomial.eval c (pderiv b (T a))

/-- The cross Hessian of the actual switched endpoint transports the
field derivative between the first and last direction bases. -/
theorem twoBasisEndpointHeight_cross_Hessian {m : ℕ}
    (T : Fin m → MvPolynomial (Fin m) ℝ) (c : Fin m → ℝ)
    (A B : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    MvPolynomial.eval (fun _ => 0)
      (pderiv (Fin.castAdd m i) (pderiv (Fin.natAdd m j) (twoBasisEndpointHeight T c A B))) =
      (A.transpose * (polynomialFieldDerivative T c).transpose * B) i j := by
  have hij : Fin.castAdd m i < Fin.natAdd m j := by
    change (i : ℕ) < m + (j : ℕ)
    omega
  rw [twoBasisEndpointHeight, switchedEndpointHeight_mixedHessian _ _ _ _ _ hij]
  simp only [Fin.append_left, Fin.append_right, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul, polynomialFieldDerivative]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Large skew in the field produces a large coefficient of an actual
Jacobian minor of the endpoint obtained from two successive direction bases. -/
theorem exists_large_twoBasisEndpointMinor_coeff {m : ℕ}
    (T : Fin m → MvPolynomial (Fin m) ℝ) (c : Fin m → ℝ)
    (A B Ai Bi : Matrix (Fin m) (Fin m) ℝ)
    (hA : A * Ai = 1) (hB : B * Bi = 1)
    (Ua Ub d η : ℝ) (hUa : 0 ≤ Ua) (hUb : 0 ≤ Ub) (hd : 0 < d) (hη : 0 ≤ η)
    (hAi : ∀ i j, |Ai i j| ≤ Ua) (hBi : ∀ i j, |Bi i j| ≤ Ub)
    (hdet : d ≤ |A.det|)
    (hskew : ∃ i j, 2 * (m : ℝ)^2 * Ua * Ub * η <
      |MvPolynomial.eval c (pderiv j (T i)) - MvPolynomial.eval c (pderiv i (T j))|) :
    ∃ j e, d * η <
      |(endpointMinorPolynomial (twoBasisEndpointHeight T c A B) A Ai B
        (Fin.castAdd m) (Fin.natAdd m) j).coeff e| := by
  have hcross := twoBasisEndpointHeight_cross_Hessian T c A B
  obtain ⟨j, e, hlarge⟩ := exists_large_endpointKernelPolynomial_coeff
    (twoBasisEndpointHeight T c A B) (Fin.castAdd m) (Fin.natAdd m)
    A B Ai Bi (polynomialFieldDerivative T c) hA hB hcross
    Ua Ub η hUa hUb hη hAi hBi (by simpa [polynomialFieldDerivative] using hskew)
  exact ⟨j, e, endpointMinorPolynomial_coeff_large_of_kernel
    (twoBasisEndpointHeight T c A B) A Ai B (Fin.castAdd m) (Fin.natAdd m)
    j e d η hd hdet hlarge⟩

end Submission.Lib.K4CubicTests
