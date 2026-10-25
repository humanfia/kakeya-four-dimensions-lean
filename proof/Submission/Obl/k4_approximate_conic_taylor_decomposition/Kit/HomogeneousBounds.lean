/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/HomogeneousBounds.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/HomogeneousBounds.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

open MvPolynomial

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

/-- Differentiation of a bounded-degree polynomial increases its coefficient
bound by at most the degree. -/
theorem coeff_pderiv_abs_le_of_totalDegree (F : MvPolynomial (Fin 3) ℝ)
    (n : ℕ) (hdeg : F.totalDegree ≤ n) (M : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ m, |F.coeff m| ≤ M) (i : Fin 3) (m : Fin 3 →₀ ℕ) :
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

private theorem abs_sum_three_le (f : Fin 3 → ℝ) (B : ℝ) (hf : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 3 * B := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B := Finset.sum_le_sum fun i _ => hf i
    _ = _ := by simp

/-- A homogeneous polynomial with bounded coefficients has a pointwise bound
with an explicit exponential factor in its degree. For the fixed degrees used
in the conic tests, this is a polynomial conditioning bound in the coordinates. -/
theorem homogeneous_eval_abs_le (A : ℝ) (hA : 0 ≤ A)
    (x : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ A) :
    ∀ (n : ℕ) (F : MvPolynomial (Fin 3) ℝ), F.IsHomogeneous n →
      ∀ M : ℝ, 0 ≤ M → (∀ m, |F.coeff m| ≤ M) →
        |MvPolynomial.eval x F| ≤ (3 : ℝ) ^ n * A ^ n * M := by
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
      have hdcoeff (i : Fin 3) (m : Fin 3 →₀ ℕ) :
          |(pderiv i F).coeff m| ≤ ((n + 1 : ℕ) : ℝ) * M :=
        coeff_pderiv_abs_le_of_totalDegree F (n + 1) hF.totalDegree_le M hM hcoeff i m
      have hd (i : Fin 3) : |MvPolynomial.eval x (pderiv i F)| ≤
          (3 : ℝ) ^ n * A ^ n * (((n + 1 : ℕ) : ℝ) * M) :=
        ih (pderiv i F) (by simpa using hF.pderiv) _ (by positivity) (hdcoeff i)
      have hterm (i : Fin 3) : |x i * MvPolynomial.eval x (pderiv i F)| ≤
          A * ((3 : ℝ) ^ n * A ^ n * (((n + 1 : ℕ) : ℝ) * M)) := by
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
        _ = |∑ i : Fin 3, x i * MvPolynomial.eval x (pderiv i F)| := congrArg abs heval.symm
        _ ≤ 3 * (A * ((3 : ℝ) ^ n * A ^ n * (((n + 1 : ℕ) : ℝ) * M))) :=
          abs_sum_three_le _ _ hterm
        _ = ((n + 1 : ℕ) : ℝ) * ((3 : ℝ) ^ (n + 1) * A ^ (n + 1) * M) := by
          rw [pow_succ, pow_succ]
          ring

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
