import Submission.Obl.k4_scalar_tangent_isotropic_improvement.FourDirections

/-! Fixed-degree coefficient and derivative comparison on a unit time block. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open Set
open scoped BigOperators

/-- Fixed-degree coefficient control from a uniform bound on the unit interval.
The inverse Vandermonde constant depends only on the degree. -/
theorem exists_polynomial_coefficients_bound (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : Polynomial ℝ) (E : ℝ), p.natDegree ≤ D → 0 ≤ E →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |p.eval x| ≤ E) → ∀ j : ℕ, |p.coeff j| ≤ C * E := by
  classical
  let v : Fin (D + 1) → ℝ := fun i => (i : ℝ) / ((D : ℝ) + 1)
  have hD : 0 < (D : ℝ) + 1 := by positivity
  have hv (i : Fin (D + 1)) : v i ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [v]
    refine ⟨div_nonneg (Nat.cast_nonneg _) hD.le, (div_le_one hD).mpr ?_⟩
    exact_mod_cast Nat.le_of_lt i.isLt
  have hinj : Function.Injective v := by
    intro i j h
    apply Fin.ext
    have hc := congrArg (fun x : ℝ => x * ((D : ℝ) + 1)) h
    dsimp [v] at hc
    field_simp [hD.ne'] at hc
    exact_mod_cast hc
  have hdet : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  let A : ℝ := |(Matrix.vandermonde v).det|⁻¹
  have hA : 0 < A := by dsimp [A]; exact inv_pos.mpr (abs_pos.mpr hdet)
  have hcond : 1 ≤ A * |(Matrix.vandermonde v).det| := by
    dsimp [A]
    rw [inv_mul_cancel₀ (abs_ne_zero.mpr hdet)]
  let C : ℝ := A * ((D + 1 : ℕ) : ℝ) * ((D + 1).factorial : ℝ)
  have hfact : 0 < ((D + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro p E hp hE hbound j
  have hmatrix : ∀ i k : Fin (D + 1), |v i ^ (k : ℕ)| ≤ 1 := by
    intro i k
    rw [abs_pow, abs_of_nonneg (hv i).1]
    exact pow_le_one₀ (hv i).1 (hv i).2
  have hsample : ∀ i : Fin (D + 1), |∑ k : Fin (D + 1), p.coeff k * v i ^ (k : ℕ)| ≤ E := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => p.coeff k * v i ^ k) (D + 1)]
    rw [← Polynomial.eval_eq_sum_range' (show p.natDegree < D + 1 by omega)]
    exact hbound _ (hv i)
  have hcoeff := coefficients_le_of_samples v (fun k => p.coeff k)
    (B := 1) (D := A) (E := E) le_rfl hA.le hE hmatrix hcond hsample
  by_cases hj : j ≤ D
  · simpa [C, mul_assoc] using hcoeff ⟨j, by omega⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < j by omega), abs_zero]
    exact mul_nonneg (by dsimp [C]; positivity) hE

/-- A coefficient bound controls the first derivative uniformly on the unit
interval, with a loss polynomial in the fixed degree. -/
theorem derivative_eval_le_of_coefficients (p : Polynomial ℝ) (D : ℕ)
    (hp : p.natDegree ≤ D) {B : ℝ} (hB : 0 ≤ B) (hcoeff : ∀ j : ℕ, |p.coeff j| ≤ B)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |p.derivative.eval x| ≤ ((D : ℝ) + 1) ^ 2 * B := by
  have hdeg : p.derivative.natDegree < D + 1 :=
    lt_of_le_of_lt ((Polynomial.natDegree_derivative_le p).trans ((Nat.sub_le _ _).trans hp)) (by omega)
  rw [Polynomial.eval_eq_sum_range' hdeg]
  calc
    |∑ j ∈ Finset.range (D + 1), p.derivative.coeff j * x ^ j| ≤
        ∑ j ∈ Finset.range (D + 1), |p.derivative.coeff j * x ^ j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (D + 1), B * ((D : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjD : (j : ℝ) + 1 ≤ (D : ℝ) + 1 := by
        exact_mod_cast (show j + 1 ≤ D + 1 by simpa using Finset.mem_range.mp hj)
      have hxpow : |x ^ j| ≤ 1 := by
        rw [abs_pow, abs_of_nonneg hx.1]
        exact pow_le_one₀ hx.1 hx.2
      rw [abs_mul, Polynomial.coeff_derivative, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) + 1)]
      calc
        |p.coeff (j + 1)| * ((j : ℝ) + 1) * |x ^ j| ≤ (B * ((D : ℝ) + 1)) * 1 :=
          mul_le_mul (mul_le_mul (hcoeff _) hjD (by positivity) hB) hxpow
            (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ = ((D : ℝ) + 1) ^ 2 * B := by simp; ring

/-- The first derivative obeys a degree-dependent uniform norm comparison. -/
theorem exists_polynomial_derivative_bound (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : Polynomial ℝ) (E : ℝ), p.natDegree ≤ D → 0 ≤ E →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |p.eval x| ≤ E) →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |p.derivative.eval x| ≤ C * E := by
  obtain ⟨C, hC, hcoeff⟩ := exists_polynomial_coefficients_bound D
  refine ⟨((D : ℝ) + 1) ^ 2 * C, by positivity, ?_⟩
  intro p E hp hE hbound x hx
  exact (derivative_eval_le_of_coefficients p D hp (mul_nonneg hC.le hE)
    (hcoeff p E hp hE hbound) x hx).trans_eq (by ring)

/-- Every fixed-order derivative is bounded by the original unit-block norm,
with a constant depending only on the degree and derivative order. -/
theorem exists_polynomial_iterated_derivative_bound (D r : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : Polynomial ℝ) (E : ℝ), p.natDegree ≤ D → 0 ≤ E →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |p.eval x| ≤ E) →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |((Polynomial.derivative^[r]) p).eval x| ≤ C * E := by
  obtain ⟨C, hC, hderiv⟩ := exists_polynomial_derivative_bound D
  refine ⟨C ^ r, pow_pos hC _, ?_⟩
  intro p E hp hE hbound
  have haux : ∀ r : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |((Polynomial.derivative^[r]) p).eval x| ≤ C ^ r * E := by
    intro n
    induction n with
    | zero => simpa using hbound
    | succ n ih =>
      have hdeg : ((Polynomial.derivative^[n]) p).natDegree ≤ D :=
        (Polynomial.natDegree_iterate_derivative p n).trans ((Nat.sub_le _ _).trans hp)
      have h := hderiv _ _ hdeg (mul_nonneg (pow_nonneg hC.le _) hE) ih
      simpa [Function.iterate_succ_apply', pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
  exact haux r

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
