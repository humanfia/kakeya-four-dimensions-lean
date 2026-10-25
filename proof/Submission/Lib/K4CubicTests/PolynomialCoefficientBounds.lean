/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.HomogeneousBounds
import Submission.Lib.K4CubicTests.ConicConditioning
import Submission.Lib.K4CubicTests.ConicHigherKernels

open MvPolynomial

namespace Submission.Lib.K4CubicTests

private theorem abs_sum_three_le (f : Fin 3 → ℝ) (B : ℝ) (hf : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 3 * B := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B := Finset.sum_le_sum fun i _ => hf i
    _ = _ := by simp

/-- Multiplying by a coordinate variable preserves a uniform coefficient bound. -/
theorem coeff_X_mul_abs_le (F : MvPolynomial (Fin 3) ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ m, |F.coeff m| ≤ M) (i : Fin 3) (m : Fin 3 →₀ ℕ) :
    |(X i * F).coeff m| ≤ M := by
  classical
  rw [coeff_X_mul']
  split_ifs
  · exact hcoeff _
  · simpa using hM

/-- Euler's identity bounds a positive-degree homogeneous polynomial's
coefficients by those of its three coordinate derivatives. -/
theorem homogeneous_coeff_abs_le_of_pderiv (F : MvPolynomial (Fin 3) ℝ)
    (n : ℕ) (hn : 1 ≤ n) (hF : F.IsHomogeneous n) (M : ℝ) (hM : 0 ≤ M)
    (hderiv : ∀ i m, |(pderiv i F).coeff m| ≤ M) (m : Fin 3 →₀ ℕ) :
    |F.coeff m| ≤ 3 * M := by
  have he := congrArg (MvPolynomial.lcoeff ℝ m) hF.sum_X_mul_pderiv
  simp only [map_sum, map_nsmul, map_smul, nsmul_eq_mul, smul_eq_mul, lcoeff_apply] at he
  rw [← map_natCast (C : ℝ →+* MvPolynomial (Fin 3) ℝ) n, coeff_C_mul] at he
  have hsum : |∑ i : Fin 3, (X i * pderiv i F).coeff m| ≤ 3 * M :=
    abs_sum_three_le _ M fun i => coeff_X_mul_abs_le (pderiv i F) M hM (hderiv i) i m
  have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    |F.coeff m| ≤ (n : ℝ) * |F.coeff m| := le_mul_of_one_le_left (abs_nonneg _) hncast
    _ = |(n : ℝ) * F.coeff m| := by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ))]
    _ = |∑ i : Fin 3, (X i * pderiv i F).coeff m| := congrArg abs he.symm
    _ ≤ _ := hsum

/-- Multiplication by a displayed linear polynomial has a uniform coefficient
bound with only three contributing terms. -/
theorem coeff_mul_linearPolynomial_abs_le (q : MvPolynomial (Fin 3) ℝ)
    (a : Fin 3 → ℝ) (Qbound η : ℝ) (hQbound : 0 ≤ Qbound) (hη : 0 ≤ η)
    (hq : ∀ m, |q.coeff m| ≤ Qbound) (ha : ∀ i, |a i| ≤ η) (m : Fin 3 →₀ ℕ) :
    |(q * linearPolynomial a).coeff m| ≤ 3 * Qbound * η := by
  classical
  have hexp : q * linearPolynomial a = ∑ i : Fin 3, C (a i) * (X i * q) := by
    simp only [linearPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hexp, coeff_sum]
  have hterm (i : Fin 3) : |(C (a i) * (X i * q)).coeff m| ≤ η * Qbound := by
    rw [coeff_C_mul, abs_mul]
    exact mul_le_mul (ha i) (coeff_X_mul_abs_le q Qbound hQbound hq i m) (abs_nonneg _) hη
  convert abs_sum_three_le _ (η * Qbound) hterm using 1 <;> ring

end Submission.Lib.K4CubicTests
