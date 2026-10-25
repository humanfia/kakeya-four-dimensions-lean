/-
Adapted from: here:root
Original proofs by session x0001.
-/
/- Generalized from the original proofs by x0001 in Root/HomogeneousBounds.lean. -/
import Mathlib

open MvPolynomial

namespace Submission.Lib.K4CubicTests

variable {ι : Type*} [Fintype ι]

/-- Differentiation of a bounded-degree polynomial increases its coefficient
bound by at most the degree. -/
theorem finite_coeff_pderiv_abs_le_of_totalDegree (F : MvPolynomial (ι) ℝ)
    (n : ℕ) (hdeg : F.totalDegree ≤ n) (M : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ m, |F.coeff m| ≤ M) (i : ι) (m : ι →₀ ℕ) :
    |(pderiv i F).coeff m| ≤ (n : ℝ) * M := by
  classical
  rw [coeff_pderiv]
  by_cases hz : F.coeff (m + Finsupp.single i 1) = 0
  · rw [hz, zero_mul, abs_zero]
    positivity
  · have hmem : m + Finsupp.single i 1 ∈ F.support := mem_support_iff.mpr hz
    have hmi : m i + 1 ≤ n := by
      have h := (le_degreeOf_of_mem_support i hmem).trans ((degreeOf_le_totalDegree F i).trans hdeg)
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using h
    have hcast : (m i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmi
    simp only [abs_mul]
    rw [abs_of_nonneg (by positivity : 0 ≤ (m i : ℝ) + 1)]
    calc
      _ ≤ M * (n : ℝ) := mul_le_mul (hcoeff _) hcast (by positivity) hM
      _ = _ := mul_comm _ _

private theorem finite_abs_sum_bound (f : ι → ℝ) (B : ℝ) (hf : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ (Fintype.card ι : ℝ) * B := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ => hf i
    _ = _ := by simp

/-- A homogeneous polynomial with bounded coefficients has a pointwise bound
with an explicit exponential factor in its degree. For the fixed degrees used
in the conic tests, this is a polynomial conditioning bound in the coordinates. -/
theorem finite_homogeneous_eval_abs_le (A : ℝ) (hA : 0 ≤ A)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ A) :
    ∀ (n : ℕ) (F : MvPolynomial (ι) ℝ), F.IsHomogeneous n →
      ∀ M : ℝ, 0 ≤ M → (∀ m, |F.coeff m| ≤ M) →
        |MvPolynomial.eval x F| ≤ (Fintype.card ι : ℝ) ^ n * A ^ n * M := by
  intro n
  induction n with
  | zero =>
      intro F hF M hM hcoeff
      have hconst : F = C (F.coeff 0) := by
        rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hF
        exact hF
      rw [hconst]
      simpa only [eval_C, pow_zero, one_mul] using hcoeff 0
  | succ n ih =>
      intro F hF M hM hcoeff
      have hdcoeff (i : ι) (m : ι →₀ ℕ) :
          |(pderiv i F).coeff m| ≤ ((n + 1 : ℕ) : ℝ) * M :=
        finite_coeff_pderiv_abs_le_of_totalDegree F (n + 1) hF.totalDegree_le M hM hcoeff i m
      have hd (i : ι) : |MvPolynomial.eval x (pderiv i F)| ≤
          (Fintype.card ι : ℝ) ^ n * A ^ n * (((n + 1 : ℕ) : ℝ) * M) :=
        ih (pderiv i F) (by simpa using hF.pderiv) _ (by positivity) (hdcoeff i)
      have hterm (i : ι) : |x i * MvPolynomial.eval x (pderiv i F)| ≤
          A * ((Fintype.card ι : ℝ) ^ n * A ^ n * (((n + 1 : ℕ) : ℝ) * M)) := by
        rw [abs_mul]
        exact mul_le_mul (hx i) (hd i) (abs_nonneg _) hA
      have heval := congrArg (MvPolynomial.eval x) hF.sum_X_mul_pderiv
      simp only [map_sum, map_mul, eval_X, map_natCast, map_nsmul, nsmul_eq_mul] at heval
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      apply le_of_mul_le_mul_left (a := ((n + 1 : ℕ) : ℝ)) _ hpos
      calc
        ((n + 1 : ℕ) : ℝ) * |MvPolynomial.eval x F| =
            |((n + 1 : ℕ) : ℝ) * MvPolynomial.eval x F| := by
          rw [abs_mul, abs_of_pos hpos]
        _ = |∑ i : ι, x i * MvPolynomial.eval x (pderiv i F)| := congrArg abs heval.symm
        _ ≤ (Fintype.card ι : ℝ) * (A * ((Fintype.card ι : ℝ) ^ n * A ^ n * (((n + 1 : ℕ) : ℝ) * M))) :=
          finite_abs_sum_bound _ _ hterm
        _ = ((n + 1 : ℕ) : ℝ) * ((Fintype.card ι : ℝ) ^ (n + 1) * A ^ (n + 1) * M) := by
          rw [pow_succ, pow_succ]
          ring

/-- Coefficient bounds control evaluation on a coordinate box for every
polynomial of bounded total degree, with an explicit dimension-degree loss. -/
theorem finite_polynomial_eval_abs_le (F : MvPolynomial ι ℝ) (D : ℕ)
    (hD : F.totalDegree ≤ D) (A M : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hcoeff : ∀ m, |F.coeff m| ≤ M) (x : ι → ℝ) (hx : ∀ i, |x i| ≤ A) :
    |MvPolynomial.eval x F| ≤ (D + 1 : ℕ) * (max 1 ((Fintype.card ι : ℝ) * A)) ^ D * M := by
  classical
  let R : ℝ := max 1 ((Fintype.card ι : ℝ) * A)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hcomp (n : ℕ) (hn : n ∈ Finset.range (F.totalDegree + 1)) :
      |MvPolynomial.eval x (homogeneousComponent n F)| ≤ R ^ D * M := by
    have hnD : n ≤ D := by have hn' := Finset.mem_range.mp hn; omega
    have hc (m : ι →₀ ℕ) : |(homogeneousComponent n F).coeff m| ≤ M := by
      rw [coeff_homogeneousComponent]
      split_ifs
      · exact hcoeff m
      · simpa using hM
    have h := finite_homogeneous_eval_abs_le A hA x hx n (homogeneousComponent n F)
      (homogeneousComponent_isHomogeneous n F) M hM hc
    have hp : (Fintype.card ι : ℝ) ^ n * A ^ n ≤ R ^ D := by
      calc
        _ = ((Fintype.card ι : ℝ) * A) ^ n := (mul_pow _ _ _).symm
        _ ≤ R ^ n := pow_le_pow_left₀ (by positivity) (le_max_right _ _) n
        _ ≤ R ^ D := pow_le_pow_right₀ hR hnD
    exact h.trans (mul_le_mul_of_nonneg_right hp hM)
  have heq := congrArg (MvPolynomial.eval x) (sum_homogeneousComponent F)
  simp only [map_sum] at heq
  calc
    |MvPolynomial.eval x F| = |∑ n ∈ Finset.range (F.totalDegree + 1),
        MvPolynomial.eval x (homogeneousComponent n F)| := congrArg abs heq.symm
    _ ≤ ∑ n ∈ Finset.range (F.totalDegree + 1),
        |MvPolynomial.eval x (homogeneousComponent n F)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (F.totalDegree + 1), R ^ D * M := Finset.sum_le_sum hcomp
    _ = (F.totalDegree + 1 : ℕ) * R ^ D * M := by simp; ring
    _ ≤ (D + 1 : ℕ) * R ^ D * M := by gcongr

end Submission.Lib.K4CubicTests
