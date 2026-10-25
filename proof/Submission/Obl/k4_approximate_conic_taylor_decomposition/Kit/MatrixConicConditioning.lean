/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/MatrixConicConditioning.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/MatrixConicConditioning.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.QuinticConditioning
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.ProjectiveFrame
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.ConicMatrix

open MvPolynomial

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

private theorem abs_sum_three_le (f : Fin 3 → ℝ) (M : ℝ) (hf : ∀ i, |f i| ≤ M) :
    |∑ i, f i| ≤ 3 * M := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum fun i _ => hf i
    _ = _ := by simp

/-- A uniform coefficient bound for a matrix quadratic. -/
theorem matrixQuadratic_coeff_abs_le (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (U : ℝ) (hU : 0 ≤ U) (hQ : ∀ i j, |Q i j| ≤ U) (m : Fin 3 →₀ ℕ) :
    |(matrixQuadratic Q).coeff m| ≤ 9 * U := by
  classical
  have hterm (i j : Fin 3) : |(C (Q i j) * X i * X j).coeff m| ≤ U := by
    rw [C_mul_X_eq_monomial]
    simp only [X, monomial_mul_monomial, coeff_monomial, mul_one]
    split_ifs
    · exact hQ i j
    · simpa using hU
  have hinner (i : Fin 3) : |∑ j : Fin 3, (C (Q i j) * X i * X j).coeff m| ≤ 3 * U :=
    abs_sum_three_le _ U (hterm i)
  simp only [matrixQuadratic, coeff_sum]
  convert abs_sum_three_le _ (3 * U) hinner using 1 <;> ring

/-- Coefficient bounds and a determinant lower bound on a symmetric quadratic
supply all conditioning data for its gradient field. -/
theorem matrixQuadratic_conditioning_data (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (U ν : ℝ) (hU : 0 ≤ U) (hν : 0 < ν) (hQsym : Q.IsSymm)
    (hQ : ∀ i j, |Q i j| ≤ U) (hdet : ν ≤ |Q.det|) :
    ∃ B : Matrix (Fin 3) (Fin 3) ℝ, B.IsSymm ∧ IsUnit B.det ∧
      (∀ x : Fin 3 → ℝ, ∀ j, MvPolynomial.eval x (pderiv j (matrixQuadratic Q)) = Matrix.mulVec B x j) ∧
      (∀ i j, |B i j| ≤ 2 * U) ∧ (∀ i j, |B⁻¹ i j| ≤ U ^ 2 / ν) := by
  let B : Matrix (Fin 3) (Fin 3) ℝ := (2 : ℝ) • Q
  have hBsym : B.IsSymm := by
    show ((2 : ℝ) • Q).transpose = (2 : ℝ) • Q
    rw [Matrix.transpose_smul, hQsym]
  have hBc (i j : Fin 3) : |B i j| ≤ 2 * U := by
    dsimp [B]
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hQ i j) (by norm_num)
  have hBd : 8 * ν ≤ |B.det| := by
    calc
      _ ≤ 8 * |Q.det| := mul_le_mul_of_nonneg_left hdet (by norm_num)
      _ = _ := by dsimp [B]; rw [Matrix.det_smul]; norm_num [abs_mul]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr (abs_pos.mp ((by positivity : 0 < 8 * ν).trans_le hBd))
  have hBinv (i j : Fin 3) : |B⁻¹ i j| ≤ U ^ 2 / ν := by
    convert matrix_inverse_three_abs_le B (2 * U) (8 * ν) (by positivity) (by positivity) hBc hBd i j using 1 <;>
      field_simp [ne_of_gt hν] <;> ring
  refine ⟨B, hBsym, hBu, ?_, hBc, hBinv⟩
  intro x j
  simpa only [B, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul] using
    eval_pderiv_matrixQuadratic_symm Q hQsym x j

/-- The quartic conditioning theorem directly in terms of a symmetric matrix,
point sizes and determinant lower bounds. The projective frame is constructed
inside the proof. -/
theorem exists_quartic_matrix_conic_approximation
    (p : Fin 7 → Fin 3 → ℝ) (A κ U ν ε : ℝ)
    (hA : 0 < A) (hκ : 0 < κ) (hU : 0 ≤ U) (hν : 0 < ν) (hε : 0 ≤ ε)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      κ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQsym : Q.IsSymm)
    (hQ : ∀ i j, |Q i j| ≤ U) (hdet : ν ≤ |Q.det|)
    (hqzero : ∀ i, MvPolynomial.eval (p i) (matrixQuadratic Q) = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 4)
    (hsmall : ∀ i j, |MvPolynomial.eval (p i) (pderiv j F)| ≤ ε) :
    ∃ r : ℝ, ∀ m : Fin 3 →₀ ℕ,
      |(F - C r * (matrixQuadratic Q) ^ 2).coeff m| ≤
        quarticConicError A κ (9 * U) (6 * A ^ 3 / κ) (2 * A ^ 2 / κ) (U ^ 2 / ν) (2 * U) A ε := by
  obtain ⟨P, α, hPu, hPc, hPi, hR, hα, hlow, hframe, hextra⟩ :=
    exists_conditioned_projective_frame p A κ hA hκ hcoord hp
  obtain ⟨B, hBsym, hBu, hgrad, hBc, hBi⟩ := matrixQuadratic_conditioning_data Q U ν hU hν hQsym hQ hdet
  have hQne : Q.det ≠ 0 := abs_pos.mp (hν.trans_le hdet)
  exact exists_quartic_conic_approximation p A κ (9 * U) (6 * A ^ 3 / κ) (2 * A ^ 2 / κ)
    (U ^ 2 / ν) (2 * U) A ε hA.le hκ (by positivity) hR (by positivity) (by positivity)
    (by positivity) hA.le hε hcoord hp (matrixQuadratic Q) (matrixQuadratic_isHomogeneous Q)
    (matrixQuadratic_ne_zero Q hQsym hQne) hqzero (matrixQuadratic_coeff_abs_le Q U hU hQ)
    B P hBu hPu hgrad α hα hlow hPi hBi hBc hPc hframe hextra F hF hsmall

/-- The quintic conditioning theorem with the frame and gradient data
constructed directly from matrix and direction bounds. -/
theorem quintic_coefficients_le_of_matrix_conic_tests
    (p : Fin 7 → Fin 3 → ℝ) (A κ U ν ε : ℝ)
    (hA : 0 < A) (hκ : 0 < κ) (hU : 0 ≤ U) (hν : 0 < ν) (hε : 0 ≤ ε)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      κ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQsym : Q.IsSymm)
    (hQ : ∀ i j, |Q i j| ≤ U) (hdet : ν ≤ |Q.det|)
    (hqzero : ∀ i, MvPolynomial.eval (p i) (matrixQuadratic Q) = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 5)
    (hsmall : ∀ i j k, |MvPolynomial.eval (p i) (pderiv j (pderiv k F))| ≤ ε) :
    ∀ m : Fin 3 →₀ ℕ, |F.coeff m| ≤
      quinticConicError A κ (9 * U) (6 * A ^ 3 / κ) (2 * A ^ 2 / κ) (U ^ 2 / ν) (2 * U) A ε := by
  obtain ⟨P, α, hPu, hPc, hPi, hR, hα, hlow, hframe, hextra⟩ :=
    exists_conditioned_projective_frame p A κ hA hκ hcoord hp
  obtain ⟨B, hBsym, hBu, hgrad, hBc, hBi⟩ := matrixQuadratic_conditioning_data Q U ν hU hν hQsym hQ hdet
  have hQne : Q.det ≠ 0 := abs_pos.mp (hν.trans_le hdet)
  exact quintic_coefficients_le_of_conic_tests p A κ (9 * U) (6 * A ^ 3 / κ) (2 * A ^ 2 / κ)
    (U ^ 2 / ν) (2 * U) A ε hA.le hκ (by positivity) hR (by positivity) (by positivity)
    (by positivity) hA.le hε hcoord hp (matrixQuadratic Q) (matrixQuadratic_isHomogeneous Q)
    (matrixQuadratic_ne_zero Q hQsym hQne) hqzero (matrixQuadratic_coeff_abs_le Q U hU hQ)
    B P hBsym hBu hPu hgrad α hα hlow hPi hBi hBc hPc hframe hextra F hF hsmall

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
