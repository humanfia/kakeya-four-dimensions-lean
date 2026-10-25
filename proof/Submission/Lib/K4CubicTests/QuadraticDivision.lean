/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.PolynomialCoefficientBounds

open MvPolynomial

namespace Submission.Lib.K4CubicTests

theorem linearPolynomial_isHomogeneous (a : Fin 3 → ℝ) :
    (linearPolynomial a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (a i) i

theorem pderiv_linearPolynomial (a : Fin 3 → ℝ) (i : Fin 3) :
    pderiv i (linearPolynomial a) = C (a i) := by
  classical
  simp [linearPolynomial, map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply, mul_ite, eq_comm]

/-- The third derivative of a quadratic times a linear form is a symmetric
sum of three Hessian-coefficient terms. -/
theorem third_pderiv_quadratic_mul_linear
    (q : MvPolynomial (Fin 3) ℝ) (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hqderiv : ∀ j, pderiv j q = linearPolynomial (fun k => B j k))
    (a : Fin 3 → ℝ) (i j k : Fin 3) :
    pderiv i (pderiv j (pderiv k (q * linearPolynomial a))) =
      C (B k j * a i + B k i * a j + B j i * a k) := by
  simp only [pderiv_mul, map_add, hqderiv, pderiv_linearPolynomial, pderiv_C,
    zero_mul, mul_zero, zero_add, add_zero]
  simp only [map_add, map_mul] <;> ring

/-- Contracting the symmetric third-derivative tensor by the inverse Hessian
recovers five times the linear coefficient. -/
theorem inverse_hessian_contraction (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hBsym : B.IsSymm) (hBdet : IsUnit B.det) (a : Fin 3 → ℝ) (i : Fin 3) :
    (∑ j : Fin 3, ∑ k : Fin 3,
      B⁻¹ j k * (B k j * a i + B k i * a j + B j i * a k)) = 5 * a i := by
  have htranspose : B.transpose = B := hBsym
  calc
    _ = (∑ j : Fin 3, (B⁻¹ * B) j j * a i) +
        (∑ j : Fin 3, (B⁻¹ * B) j i * a j) +
        (∑ k : Fin 3, (B.transpose * B⁻¹) i k * a k) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
      ring
    _ = _ := by
      rw [Matrix.nonsing_inv_mul B hBdet, htranspose, Matrix.mul_nonsing_inv B hBdet]
      norm_num [Matrix.one_apply] <;> ring

private theorem abs_double_sum_three_le (f : Fin 3 → Fin 3 → ℝ)
    (M : ℝ) (hf : ∀ j k, |f j k| ≤ M) : |∑ j, ∑ k, f j k| ≤ 9 * M := by
  have hsum (g : Fin 3 → ℝ) (N : ℝ) (hg : ∀ i, |g i| ≤ N) : |∑ i, g i| ≤ 3 * N := by
    calc
      _ ≤ ∑ i, |g i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, N := Finset.sum_le_sum fun i _ => hg i
      _ = _ := by simp
  have hinner (j : Fin 3) := hsum (f j) M (hf j)
  convert hsum (fun j => ∑ k, f j k) (3 * M) hinner using 1 <;> ring

/-- Division by a nonsingular quadratic on the linear subspace has explicit
conditioning. A Hessian contraction gives the bound without choosing a largest
coefficient of the quadratic or performing polynomial long division. -/
theorem linear_coefficients_le_of_quadratic_product
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2)
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hBsym : B.IsSymm) (hBdet : IsUnit B.det)
    (hqderiv : ∀ j, pderiv j q = linearPolynomial (fun k => B j k))
    (a : Fin 3 → ℝ) (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hBinv : ∀ j k, |B⁻¹ j k| ≤ T)
    (hcoeff : ∀ m, |(q * linearPolynomial a).coeff m| ≤ M) :
    ∀ i, |a i| ≤ 54 * T * M := by
  let H := q * linearPolynomial a
  have hH : H.IsHomogeneous 3 := hq.mul (linearPolynomial_isHomogeneous a)
  have h1hom (k : Fin 3) : (pderiv k H).IsHomogeneous 2 := by simpa using hH.pderiv
  have h2hom (j k : Fin 3) : (pderiv j (pderiv k H)).IsHomogeneous 1 := by
    simpa using (h1hom k).pderiv
  have h1 (k : Fin 3) (m : Fin 3 →₀ ℕ) : |(pderiv k H).coeff m| ≤ 3 * M :=
    coeff_pderiv_abs_le_of_totalDegree H 3 hH.totalDegree_le M hM hcoeff k m
  have h2 (j k : Fin 3) (m : Fin 3 →₀ ℕ) : |(pderiv j (pderiv k H)).coeff m| ≤ 6 * M := by
    convert coeff_pderiv_abs_le_of_totalDegree (pderiv k H) 2 (h1hom k).totalDegree_le
      (3 * M) (by positivity) (h1 k) j m using 1 <;> ring
  have h3 (i j k : Fin 3) : |(pderiv i (pderiv j (pderiv k H))).coeff 0| ≤ 6 * M := by
    simpa using coeff_pderiv_abs_le_of_totalDegree (pderiv j (pderiv k H)) 1
      (h2hom j k).totalDegree_le (6 * M) (by positivity) (h2 j k) i 0
  have hthird (i j k : Fin 3) : |B k j * a i + B k i * a j + B j i * a k| ≤ 6 * M := by
    have h := h3 i j k
    change |(pderiv i (pderiv j (pderiv k (q * linearPolynomial a)))).coeff 0| ≤ 6 * M at h
    rw [third_pderiv_quadratic_mul_linear q B hqderiv a i j k] at h
    simpa using h
  intro i
  have hsum : |∑ j : Fin 3, ∑ k : Fin 3,
      B⁻¹ j k * (B k j * a i + B k i * a j + B j i * a k)| ≤ 54 * T * M := by
    have hterm (j k : Fin 3) :
        |B⁻¹ j k * (B k j * a i + B k i * a j + B j i * a k)| ≤ T * (6 * M) := by
      rw [abs_mul]
      exact mul_le_mul (hBinv j k) (hthird i j k) (abs_nonneg _) hT
    convert abs_double_sum_three_le _ (T * (6 * M)) hterm using 1 <;> ring
  have h5 : 5 * |a i| ≤ 54 * T * M := by
    calc
      _ = |5 * a i| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
      _ = |∑ j : Fin 3, ∑ k : Fin 3,
          B⁻¹ j k * (B k j * a i + B k i * a j + B j i * a k)| :=
        congrArg abs (inverse_hessian_contraction B hBsym hBdet a i).symm
      _ ≤ _ := hsum
  linarith [abs_nonneg (a i)]

end Submission.Lib.K4CubicTests
