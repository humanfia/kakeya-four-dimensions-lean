/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.ConicHigherKernels

open MvPolynomial

namespace Submission.Lib.K4CubicTests

/-- The homogeneous quadratic associated to a symmetric matrix. -/
noncomputable def matrixQuadratic (Q : Matrix (Fin 3) (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, C (Q i j) * X i * X j

theorem matrixQuadratic_isHomogeneous (Q : Matrix (Fin 3) (Fin 3) ℝ) :
    (matrixQuadratic Q).IsHomogeneous 2 := by
  exact IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun j _ =>
    (isHomogeneous_C_mul_X (Q i j) i).mul (isHomogeneous_X ℝ j)

theorem eval_matrixQuadratic (Q : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (matrixQuadratic Q) = ∑ i : Fin 3, ∑ j : Fin 3, x i * Q i j * x j := by
  simp [matrixQuadratic, mul_comm, mul_left_comm, mul_assoc]

theorem eval_pderiv_matrixQuadratic (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (x : Fin 3 → ℝ) (j : Fin 3) :
    MvPolynomial.eval x (pderiv j (matrixQuadratic Q)) =
      (∑ k : Fin 3, Q j k * x k) + ∑ k : Fin 3, Q k j * x k := by
  fin_cases j <;>
    simp [matrixQuadratic, Fin.sum_univ_succ, pderiv_mul, pderiv_C_mul, pderiv_C] <;> ring

theorem eval_pderiv_matrixQuadratic_symm (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm)
    (x : Fin 3 → ℝ) (j : Fin 3) :
    MvPolynomial.eval x (pderiv j (matrixQuadratic Q)) = 2 * Matrix.mulVec Q x j := by
  rw [eval_pderiv_matrixQuadratic]
  have hsum : (∑ k : Fin 3, Q k j * x k) = ∑ k : Fin 3, Q j k * x k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hQ.apply j k]
  rw [hsum]
  simp only [Matrix.mulVec, dotProduct]
  ring

/-- A nonsingular symmetric matrix supplies the nondegenerate gradient map
required by the polynomial conic-kernel lemmas. -/
theorem matrixQuadratic_gradient_equiv (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q.IsSymm) (hdet : Q.det ≠ 0) :
    ∃ B : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ),
      ∀ (x : Fin 3 → ℝ) (j : Fin 3),
        MvPolynomial.eval x (pderiv j (matrixQuadratic Q)) = B x j := by
  have hunit : IsUnit ((2 : ℝ) • Q).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  let B : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 3)) ((2 : ℝ) • Q) hunit
  refine ⟨B, ?_⟩
  intro x j
  change MvPolynomial.eval x (pderiv j (matrixQuadratic Q)) =
    Matrix.toLin (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3)) ((2 : ℝ) • Q) x j
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  exact eval_pderiv_matrixQuadratic_symm Q hQ x j

theorem matrixQuadratic_ne_zero (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q.IsSymm) (hdet : Q.det ≠ 0) : matrixQuadratic Q ≠ 0 := by
  obtain ⟨B, hB⟩ := matrixQuadratic_gradient_equiv Q hQ hdet
  intro hz
  have h := hB (B.symm (Pi.single (0 : Fin 3) (1 : ℝ))) 0
  simp [hz] at h

/-- The cubic conic kernel in the symmetric-matrix representation. -/
theorem cubic_matrix_conic_kernel (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm) (hdet : Q.det ≠ 0)
    (hQzero : ∀ i : Fin 7, (∑ a : Fin 3, ∑ b : Fin 3, p i a * Q a b * p i b) = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 3)
    (hFzero : ∀ i, MvPolynomial.eval (p i) F = 0) :
    ∃ L : MvPolynomial (Fin 3) ℝ, L.IsHomogeneous 1 ∧ F = matrixQuadratic Q * L := by
  apply cubic_vanishing_eq_conic_mul_linear p hp (matrixQuadratic Q)
    (matrixQuadratic_isHomogeneous Q) (matrixQuadratic_ne_zero Q hQ hdet) ?_ F hF hFzero
  intro i
  rw [eval_matrixQuadratic]
  exact hQzero i

/-- The quartic conic kernel in the symmetric-matrix representation. -/
theorem quartic_matrix_conic_kernel (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm) (hdet : Q.det ≠ 0)
    (hQzero : ∀ i : Fin 7, (∑ a : Fin 3, ∑ b : Fin 3, p i a * Q a b * p i b) = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 4)
    (hFzero : ∀ i : Fin 7, ∀ j : Fin 3, MvPolynomial.eval (p i) (pderiv j F) = 0) :
    ∃ r : ℝ, F = C r * matrixQuadratic Q ^ 2 := by
  obtain ⟨B, hB⟩ := matrixQuadratic_gradient_equiv Q hQ hdet
  apply quartic_vanishing_eq_conic_sq p hp (matrixQuadratic Q)
    (matrixQuadratic_isHomogeneous Q) (matrixQuadratic_ne_zero Q hQ hdet) ?_ B hB F hF hFzero
  intro i
  rw [eval_matrixQuadratic]
  exact hQzero i

/-- The quintic conic kernel in the symmetric-matrix representation. -/
theorem quintic_matrix_conic_kernel (p : Fin 7 → Fin 3 → ℝ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm) (hdet : Q.det ≠ 0)
    (hQzero : ∀ i : Fin 7, (∑ a : Fin 3, ∑ b : Fin 3, p i a * Q a b * p i b) = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 5)
    (hFzero : ∀ i : Fin 7, ∀ j k : Fin 3,
      MvPolynomial.eval (p i) (pderiv k (pderiv j F)) = 0) : F = 0 := by
  obtain ⟨B, hB⟩ := matrixQuadratic_gradient_equiv Q hQ hdet
  apply quintic_vanishing_eq_zero p hp (matrixQuadratic Q)
    (matrixQuadratic_isHomogeneous Q) (matrixQuadratic_ne_zero Q hQ hdet) ?_ B hB F hF hFzero
  intro i
  rw [eval_matrixQuadratic]
  exact hQzero i

end Submission.Lib.K4CubicTests
