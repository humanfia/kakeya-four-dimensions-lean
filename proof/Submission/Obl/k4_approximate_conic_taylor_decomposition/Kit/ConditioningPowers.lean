/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/ConditioningPowers.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/ConditioningPowers.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.MatrixConicConditioning

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

noncomputable def normalizedQuarticError (A X ε : ℝ) : ℝ :=
  quarticConicError A A⁻¹ (9 * X) (6 * A ^ 3 / A⁻¹) (2 * A ^ 2 / A⁻¹)
    (X ^ 2 / X⁻¹) (2 * X) A ε

noncomputable def normalizedQuinticError (A X ε : ℝ) : ℝ :=
  quinticConicError A A⁻¹ (9 * X) (6 * A ^ 3 / A⁻¹) (2 * A ^ 2 / A⁻¹)
    (X ^ 2 / X⁻¹) (2 * X) A ε

theorem normalizedQuarticError_eq (A X ε : ℝ) : normalizedQuarticError A X ε =
    4536 * A ^ 9 * ε + 1499596235182080 * A ^ 37 * X ^ 8 * ε := by
  simp only [normalizedQuarticError, quarticConicError, quarticParallelError, cubicConicError,
    div_eq_mul_inv, inv_pow, inv_inv]
  ring

theorem normalizedQuinticError_eq (A X ε : ℝ) : normalizedQuinticError A X ε =
    (629856 * X ^ 8 + 3) * normalizedQuarticError A X ε := by
  simp only [normalizedQuinticError, quinticConicError, normalizedQuarticError,
    div_eq_mul_inv, inv_pow, inv_inv]
  ring

theorem normalizedQuarticError_le_monomial (A X ε : ℝ)
    (hA : 1 ≤ A) (hX : 1 ≤ X) (hε : 0 ≤ ε) :
    normalizedQuarticError A X ε ≤ 1499596235186616 * A ^ 37 * X ^ 8 * ε := by
  have hA0 : 0 ≤ A := by linarith
  have hpow : A ^ 9 ≤ A ^ 37 := pow_le_pow_right₀ hA (by decide)
  have hX8 : 1 ≤ X ^ 8 := one_le_pow₀ hX
  rw [normalizedQuarticError_eq]
  calc
    _ ≤ 4536 * A ^ 37 * X ^ 8 * ε + 1499596235182080 * A ^ 37 * X ^ 8 * ε := by
      apply add_le_add _ le_rfl
      calc
        4536 * A ^ 9 * ε ≤ 4536 * A ^ 37 * ε := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity) hX8) hε
    _ = _ := by ring

theorem normalizedQuinticError_le_monomial (A X ε : ℝ)
    (hA : 1 ≤ A) (hX : 1 ≤ X) (hε : 0 ≤ ε) :
    normalizedQuinticError A X ε ≤ 944534185098406767144 * A ^ 37 * X ^ 16 * ε := by
  have hA0 : 0 ≤ A := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hX8 : 1 ≤ X ^ 8 := one_le_pow₀ hX
  have hfactor : 629856 * X ^ 8 + 3 ≤ 629859 * X ^ 8 := by nlinarith
  have hE : 0 ≤ normalizedQuarticError A X ε := by rw [normalizedQuarticError_eq]; positivity
  rw [normalizedQuinticError_eq]
  calc
    _ ≤ (629859 * X ^ 8) * (1499596235186616 * A ^ 37 * X ^ 8 * ε) :=
      mul_le_mul hfactor (normalizedQuarticError_le_monomial A X ε hA hX hε) hE (by positivity)
    _ = _ := by ring

theorem normalizedQuarticError_le_power (A : ℝ) (hA : 2 ≤ A) (m : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    normalizedQuarticError A (A ^ m) ε ≤ A ^ (137 + 8 * m) * ε := by
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hC : (1499596235186616 : ℝ) ≤ A ^ 100 :=
    (show (1499596235186616 : ℝ) ≤ 2 ^ 100 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hA 100)
  calc
    _ ≤ 1499596235186616 * A ^ 37 * (A ^ m) ^ 8 * ε :=
      normalizedQuarticError_le_monomial A (A ^ m) ε hA1 (one_le_pow₀ hA1) hε
    _ ≤ A ^ 100 * A ^ 37 * (A ^ m) ^ 8 * ε := by gcongr
    _ = _ := by
      rw [← pow_add, ← pow_mul, ← pow_add]
      congr 2
      omega

theorem normalizedQuinticError_le_power (A : ℝ) (hA : 2 ≤ A) (m : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    normalizedQuinticError A (A ^ m) ε ≤ A ^ (137 + 16 * m) * ε := by
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hC : (944534185098406767144 : ℝ) ≤ A ^ 100 :=
    (show (944534185098406767144 : ℝ) ≤ 2 ^ 100 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hA 100)
  calc
    _ ≤ 944534185098406767144 * A ^ 37 * (A ^ m) ^ 16 * ε :=
      normalizedQuinticError_le_monomial A (A ^ m) ε hA1 (one_le_pow₀ hA1) hε
    _ ≤ A ^ 100 * A ^ 37 * (A ^ m) ^ 16 * ε := by gcongr
    _ = _ := by
      rw [← pow_add, ← pow_mul, ← pow_add]
      congr 2
      omega

/-- A quartic conic approximation with a single power loss, from the
standard point and matrix conditioning assumptions. -/
theorem exists_quartic_approximation_power_bound
    (p : Fin 7 → Fin 3 → ℝ) (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε) (d : ℕ)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      A⁻¹ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQsym : Q.IsSymm)
    (hQ : ∀ i j, |Q i j| ≤ A ^ d) (hdet : (A ^ d)⁻¹ ≤ |Q.det|)
    (hqzero : ∀ i, MvPolynomial.eval (p i) (matrixQuadratic Q) = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 4)
    (hsmall : ∀ i j, |MvPolynomial.eval (p i) (MvPolynomial.pderiv j F)| ≤ ε) :
    ∃ r : ℝ, ∀ m : Fin 3 →₀ ℕ,
      |(F - MvPolynomial.C r * (matrixQuadratic Q) ^ 2).coeff m| ≤ A ^ (137 + 8 * d) * ε := by
  have hApos : 0 < A := by linarith
  obtain ⟨r, hr⟩ := exists_quartic_matrix_conic_approximation p A A⁻¹ (A ^ d) (A ^ d)⁻¹ ε
    hApos (by positivity) (by positivity) (by positivity) hε hcoord hp Q hQsym hQ hdet hqzero F hF hsmall
  exact ⟨r, fun m => (hr m).trans (normalizedQuarticError_le_power A hA d ε hε)⟩

/-- Quintic injectivity with a single power loss and no projective frame
or inverse matrix data required from the caller. -/
theorem quintic_coefficients_le_power_bound
    (p : Fin 7 → Fin 3 → ℝ) (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε) (d : ℕ)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      A⁻¹ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQsym : Q.IsSymm)
    (hQ : ∀ i j, |Q i j| ≤ A ^ d) (hdet : (A ^ d)⁻¹ ≤ |Q.det|)
    (hqzero : ∀ i, MvPolynomial.eval (p i) (matrixQuadratic Q) = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 5)
    (hsmall : ∀ i j k, |MvPolynomial.eval (p i) (MvPolynomial.pderiv j (MvPolynomial.pderiv k F))| ≤ ε) :
    ∀ m : Fin 3 →₀ ℕ, |F.coeff m| ≤ A ^ (137 + 16 * d) * ε := by
  have hApos : 0 < A := by linarith
  intro m
  exact (quintic_coefficients_le_of_matrix_conic_tests p A A⁻¹ (A ^ d) (A ^ d)⁻¹ ε
    hApos (by positivity) (by positivity) (by positivity) hε hcoord hp Q hQsym hQ hdet hqzero F hF hsmall m).trans
      (normalizedQuinticError_le_power A hA d ε hε)

/-- Cubic conic approximation with a uniform power loss. This kernel
estimate does not require an inverse bound for the conic itself. -/
theorem exists_cubic_conic_approximation_power_bound
    (p : Fin 7 → Fin 3 → ℝ) (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      A⁻¹ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) (hne : q ≠ 0)
    (hqzero : ∀ i, MvPolynomial.eval (p i) q = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 3)
    (hsmall : ∀ i, |MvPolynomial.eval (p i) F| ≤ ε) :
    ∃ L : MvPolynomial (Fin 3) ℝ, L.IsHomogeneous 1 ∧
      ∀ m : Fin 3 →₀ ℕ, |(F - q * L).coeff m| ≤ A ^ 109 * ε := by
  have hApos : 0 < A := by linarith
  obtain ⟨L, hL, hcoeff⟩ := exists_cubic_conic_approximation p A A⁻¹ ε hApos.le (by positivity)
    hε hcoord hp q hq hne hqzero F hF hsmall
  have hC : (1512 : ℝ) ≤ A ^ 100 :=
    (show (1512 : ℝ) ≤ 2 ^ 100 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hA 100)
  refine ⟨L, hL, ?_⟩
  intro m
  calc
    _ ≤ 1512 * A ^ 6 / (A⁻¹) ^ 3 * ε := hcoeff m
    _ = 1512 * A ^ 9 * ε := by simp only [div_eq_mul_inv, inv_pow, inv_inv]; ring
    _ ≤ A ^ 100 * A ^ 9 * ε := by gcongr
    _ = _ := by ring

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
