import Submission.Obl.k4_approximate_conic_taylor_decomposition.LinearNorming
import Submission.Obl.k4_approximate_conic_taylor_decomposition.QuadraticNorming
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.QuadraticDivision
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.MatrixConicConditioning

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

open MvPolynomial

/-- Realize a homogeneous linear polynomial as a continuous linear form. -/
noncomputable def polyLinearForm (P : MvPolynomial (Fin 3) ℝ) : E3 →L[ℝ] ℝ :=
  linearForm (fun i => (pderiv i P).coeff 0)

lemma polyLinearForm_apply (P : MvPolynomial (Fin 3) ℝ) (hP : P.IsHomogeneous 1) (u : E3) :
    polyLinearForm P u = eval (fun i => u i) P := by
  conv_rhs => rw [Kit.homogeneous_one_eq_sum_linear P hP]
  simp [polyLinearForm, linearForm_apply]

/-- Quantitative division by a nonsingular quadratic bounds the linear factor's norm. -/
lemma polyLinearForm_norm_le_of_product (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm)
    (P : MvPolynomial (Fin 3) ℝ) (hP : P.IsHomogeneous 1)
    {U ν M : ℝ} (hU : 0 ≤ U) (hν : 0 < ν) (hM : 0 ≤ M)
    (hentry : ∀ i j, |Q i j| ≤ U) (hdet : ν ≤ |Q.det|)
    (hprod : ∀ m, |(Kit.matrixQuadratic Q * P).coeff m| ≤ M) :
    ‖polyLinearForm P‖ ≤ 162 * (U ^ 2 / ν) * M := by
  let a : Fin 3 → ℝ := fun i => (pderiv i P).coeff 0
  have hrepr : P = Kit.linearPolynomial a := Kit.homogeneous_one_eq_sum_linear P hP
  obtain ⟨B, hBsym, hBunit, hgrad, hBentry, hBinv⟩ :=
    Kit.matrixQuadratic_conditioning_data Q U ν hU hν hQ hentry hdet
  have hderiv (j : Fin 3) :
      pderiv j (Kit.matrixQuadratic Q) = Kit.linearPolynomial (fun k => B j k) := by
    apply MvPolynomial.funext
    intro x
    rw [hgrad]
    simp only [Kit.linearPolynomial, map_sum, map_mul, eval_C, eval_X,
      Matrix.mulVec, dotProduct]
  have hcoeff := Kit.linear_coefficients_le_of_quadratic_product (Kit.matrixQuadratic Q)
    (Kit.matrixQuadratic_isHomogeneous Q) B hBsym hBunit hderiv a (U ^ 2 / ν) M
    (by positivity) hM hBinv (by simpa only [← hrepr] using hprod)
  calc
    ‖polyLinearForm P‖ ≤ 3 * (54 * (U ^ 2 / ν) * M) := linearForm_norm_le (by positivity) hcoeff
    _ = 162 * (U ^ 2 / ν) * M := by ring

/-- A coefficient approximation by a cubic conic product controls its linear factor. -/
lemma polyLinearForm_norm_le_power (J d : ℕ) (hJ : 9 ≤ J)
    {A ε : ℝ} (hA : 2 ≤ A) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm)
    (hentry : ∀ i j, |Q i j| ≤ A ^ 4) (hdet : (A ^ d)⁻¹ ≤ |Q.det|)
    (F P : MvPolynomial (Fin 3) ℝ) (hP : P.IsHomogeneous 1)
    (hFcoeff : ∀ m, |F.coeff m| ≤ A ^ 9)
    (herror : ∀ m, |(F - Kit.matrixQuadratic Q * P).coeff m| ≤ A ^ J * ε) :
    ‖polyLinearForm P‖ ≤ A ^ (J + d + 17) := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hprod (m : Fin 3 →₀ ℕ) : |(Kit.matrixQuadratic Q * P).coeff m| ≤ A ^ (J + 1) := by
    have heq : (Kit.matrixQuadratic Q * P).coeff m =
        F.coeff m - (F - Kit.matrixQuadratic Q * P).coeff m := by
      simp only [coeff_sub]
      ring
    rw [heq]
    calc
      _ ≤ |F.coeff m| + |(F - Kit.matrixQuadratic Q * P).coeff m| := abs_sub _ _
      _ ≤ A ^ 9 + A ^ J * ε := add_le_add (hFcoeff m) (herror m)
      _ ≤ A ^ J + A ^ J := add_le_add (pow_le_pow_right₀ hA1 hJ)
        (mul_le_of_le_one_right (pow_nonneg hA0.le J) hε1)
      _ ≤ A * A ^ J := by nlinarith only [hA, pow_nonneg hA0.le J]
      _ = A ^ (J + 1) := by ring
  have hb := polyLinearForm_norm_le_of_product Q hQ P hP
    (pow_nonneg hA0.le 4) (inv_pos.mpr (pow_pos hA0 d)) (pow_nonneg hA0.le _)
    hentry hdet hprod
  calc
    ‖polyLinearForm P‖ ≤ 162 * ((A ^ 4) ^ 2 / (A ^ d)⁻¹) * A ^ (J + 1) := hb
    _ = 162 * A ^ (J + d + 9) := by simp only [div_inv_eq_mul, ← pow_mul]; ring
    _ ≤ A ^ 8 * A ^ (J + d + 9) := mul_le_mul_of_nonneg_right (by
      calc (162 : ℝ) ≤ 2 ^ 8 := by norm_num
           _ ≤ A ^ 8 := pow_le_pow_left₀ (by norm_num) hA 8) (pow_nonneg hA0.le _)
    _ = A ^ (J + d + 17) := by rw [← pow_add]; congr 1; omega

/-- A quartic coefficient approximation controls the coefficient of the squared conic. -/
lemma scalar_norm_le_power (J : ℕ) (hJ : 9 ≤ J)
    {A ε lam : ℝ} (hA : 2 ≤ A) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q.IsSymm)
    (hlower : (A ^ 4)⁻¹ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |Q i j|)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 4)
    (hFcoeff : ∀ m, |F.coeff m| ≤ A ^ 9)
    (herror : ∀ m, |(F - C lam * (Kit.matrixQuadratic Q) ^ 2).coeff m| ≤ A ^ J * ε) :
    |lam| ≤ A ^ (J + 29) := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  apply abs_scalar_le_power_of_quadratic_square_bound (J + 12) hQ hA hlower
  intro u hu
  have hcoord (i : Fin 3) : |u i| ≤ 2 := (abs_apply_le_norm u i).trans (by simpa using hu)
  have hFvalue : |eval (fun i => u i) F| ≤ 1296 * A ^ J := by
    have ht := Kit.homogeneous_eval_abs_le 2 (by norm_num) (fun i => u i) hcoord 4 F hF
      (A ^ 9) (pow_nonneg hA0.le _) hFcoeff
    norm_num only [show (3 : ℝ) ^ 4 = 81 by norm_num, show (2 : ℝ) ^ 4 = 16 by norm_num, show (81 : ℝ) * 16 = 1296 by norm_num] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA1 hJ) (by norm_num))
  have hEhom : (F - C lam * (Kit.matrixQuadratic Q) ^ 2).IsHomogeneous 4 := by
    exact hF.sub (((Kit.matrixQuadratic_isHomogeneous Q).pow 2).C_mul lam)
  have hEvalue : |eval (fun i => u i) (F - C lam * (Kit.matrixQuadratic Q) ^ 2)| ≤ 1296 * A ^ J := by
    have ht := Kit.homogeneous_eval_abs_le 2 (by norm_num) (fun i => u i) hcoord 4
      (F - C lam * (Kit.matrixQuadratic Q) ^ 2) hEhom
      (A ^ J * ε) (by positivity) herror
    norm_num only [show (3 : ℝ) ^ 4 = 81 by norm_num, show (2 : ℝ) ^ 4 = 16 by norm_num, show (81 : ℝ) * 16 = 1296 by norm_num] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (pow_nonneg hA0.le _) hε1) (by norm_num))
  have heq : lam * (Submission.Obl.k4_real_conic_restoration.quad Q (fun i => u i)) ^ 2 =
      eval (fun i => u i) F - eval (fun i => u i) (F - C lam * (Kit.matrixQuadratic Q) ^ 2) := by
    simp only [map_sub, map_mul, eval_C, map_pow, Kit.eval_matrixQuadratic,
      Submission.Obl.k4_real_conic_restoration.quad]
    ring
  rw [heq]
  calc
    _ ≤ |eval (fun i => u i) F| + |eval (fun i => u i) (F - C lam * (Kit.matrixQuadratic Q) ^ 2)| := abs_sub _ _
    _ ≤ 1296 * A ^ J + 1296 * A ^ J := add_le_add hFvalue hEvalue
    _ = 2592 * A ^ J := by ring
    _ ≤ A ^ 12 * A ^ J := mul_le_mul_of_nonneg_right (by
      calc (2592 : ℝ) ≤ 2 ^ 12 := by norm_num
           _ ≤ A ^ 12 := pow_le_pow_left₀ (by norm_num) hA 12) (pow_nonneg hA0.le _)
    _ = A ^ (J + 12) := by rw [← pow_add, add_comm]

end Submission.Obl.k4_approximate_conic_taylor_decomposition
