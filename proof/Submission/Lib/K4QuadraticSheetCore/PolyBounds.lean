import Mathlib
import Submission.Lib.K4ChartLifting.PolyAlgebra
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm

/-! Adapted from: here:o223 (session x0777, branch x0777). -/

/-!
# Elementary bounds for real polynomials on the unit cube

The coefficient `ℓ¹` norm `coeffL1` bounds values on the cube `[-1,1]ⁿ`, partial derivatives
lose at most the total degree, and the coefficient norm gives a Lipschitz bound in the
`ℓ¹` distance. Conversely a value bound on `[0,1]ⁿ` bounds the coefficient norm with a
constant depending only on dimension and degree.
-/

namespace Submission.Lib.K4QuadraticSheetCore

open MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

section Products

theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have ha' : ∀ i ∈ s, |a i| ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, |b i| ≤ 1 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hpa : |∏ i ∈ s, a i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) ha'
    have hbj : |b j| ≤ 1 := hb j (Finset.mem_insert_self j s)
    have hrec := ih ha' hb'
    calc
      |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
          = |(a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| := by
            congr 1; ring
      _ ≤ |a j - b j| * |∏ i ∈ s, a i| + |b j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a j - b j| * 1 + 1 * ∑ i ∈ s, |a i - b i| := by
            gcongr
      _ = _ := by ring

theorem abs_pow_sub_pow_le (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (n : ℕ) :
    |x ^ n - y ^ n| ≤ n * |x - y| := by
  have h := abs_prod_sub_prod_le (Finset.range n) (fun _ => x) (fun _ => y)
    (fun _ _ => hx) (fun _ _ => hy)
  simpa only [Finset.prod_const, Finset.card_range, Finset.sum_const, nsmul_eq_mul] using h

end Products

section Cube

variable {n : ℕ}

theorem abs_monomial_eval_le_one (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) (m : Fin n →₀ ℕ) :
    |∏ i, x i ^ m i| ≤ 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro i _
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (hx i)

/-- Values on the cube `[-1,1]ⁿ` are bounded by the coefficient norm. -/
theorem abs_eval_le_coeffL1 (Q : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) : |eval x Q| ≤ coeffL1 Q := by
  rw [eval_eq']
  calc
    |∑ d ∈ Q.support, Q.coeff d * ∏ i, x i ^ d i| ≤
        ∑ d ∈ Q.support, |Q.coeff d * ∏ i, x i ^ d i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Q.support, |Q.coeff d| := by
        apply Finset.sum_le_sum
        intro d _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_monomial_eval_le_one x hx d)
    _ = coeffL1 Q := rfl

theorem monomial_degree_le {Q : MvPolynomial (Fin n) ℝ} {d : Fin n →₀ ℕ} (hd : d ∈ Q.support)
    (i : Fin n) : d i ≤ Q.totalDegree := by
  have h1 : d i ≤ d.sum (fun _ e => e) := by
    classical
    by_cases hi : i ∈ d.support
    · exact Finset.single_le_sum (f := fun j => d j) (fun _ _ => Nat.zero_le _) hi
    · simp [Finsupp.notMem_support_iff.mp hi]
  exact h1.trans (le_totalDegree hd)

/-- A partial derivative costs at most the total degree in the coefficient norm. -/
theorem coeffL1_pderiv_le (Q : MvPolynomial (Fin n) ℝ) (k : Fin n) :
    coeffL1 (pderiv k Q) ≤ Q.totalDegree * coeffL1 Q := by
  classical
  unfold coeffL1
  have hmap : ∀ m ∈ (pderiv k Q).support, m + Finsupp.single k 1 ∈ Q.support := by
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    exact mem_support_iff.mpr (left_ne_zero_of_mul hm)
  have hinj : Set.InjOn (fun m : Fin n →₀ ℕ => m + Finsupp.single k 1)
      (pderiv k Q).support := fun a _ b _ hab => add_right_cancel hab
  calc
    ∑ m ∈ (pderiv k Q).support, |(pderiv k Q).coeff m| ≤
        ∑ m ∈ (pderiv k Q).support,
          (Q.totalDegree : ℝ) * |Q.coeff (m + Finsupp.single k 1)| := by
        apply Finset.sum_le_sum
        intro m hm
        rw [coeff_pderiv, abs_mul, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have hdeg := monomial_degree_le (hmap m hm) k
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hdeg
        rw [abs_of_nonneg (by positivity)]
        exact_mod_cast hdeg
    _ = (Q.totalDegree : ℝ) * ∑ m ∈ (pderiv k Q).support, |Q.coeff (m + Finsupp.single k 1)| := by
        rw [Finset.mul_sum]
    _ ≤ (Q.totalDegree : ℝ) * ∑ m' ∈ Q.support, |Q.coeff m'| := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Finset.sum_image (f := fun m' => |Q.coeff m'|) hinj]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m' hm'
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
          exact hmap m hm
        · intro _ _ _; exact abs_nonneg _

/-- The coefficient norm gives a Lipschitz bound on the cube `[-1,1]ⁿ` in the `ℓ¹` distance. -/
theorem abs_eval_sub_eval_le (Q : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) :
    |eval x Q - eval y Q| ≤ Q.totalDegree * coeffL1 Q * ∑ i, |x i - y i| := by
  rw [eval_eq', eval_eq', ← Finset.sum_sub_distrib]
  have hS : 0 ≤ ∑ i, |x i - y i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc
    |∑ d ∈ Q.support, (Q.coeff d * ∏ i, x i ^ d i - Q.coeff d * ∏ i, y i ^ d i)| ≤
        ∑ d ∈ Q.support, |Q.coeff d * ∏ i, x i ^ d i - Q.coeff d * ∏ i, y i ^ d i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Q.support, |Q.coeff d| * ((Q.totalDegree : ℝ) * ∑ i, |x i - y i|) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [← mul_sub, abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc
          |∏ i, x i ^ d i - ∏ i, y i ^ d i| ≤ ∑ i, |x i ^ d i - y i ^ d i| :=
            abs_prod_sub_prod_le _ _ _
              (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hx i))
              (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hy i))
          _ ≤ ∑ i, (d i : ℝ) * |x i - y i| :=
            Finset.sum_le_sum fun i _ => abs_pow_sub_pow_le _ _ (hx i) (hy i) _
          _ ≤ ∑ i, (Q.totalDegree : ℝ) * |x i - y i| := by
            apply Finset.sum_le_sum
            intro i _
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact_mod_cast monomial_degree_le hd i
          _ = (Q.totalDegree : ℝ) * ∑ i, |x i - y i| := by rw [Finset.mul_sum]
    _ = Q.totalDegree * coeffL1 Q * ∑ i, |x i - y i| := by
        rw [← Finset.sum_mul]; unfold coeffL1; ring

/-- A value bound on the unit cube `[0,1]ⁿ` bounds the coefficient norm. -/
theorem exists_coeffL1_bound_on_unit_cube (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : MvPolynomial (Fin n) ℝ), Q.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, |eval x Q| ≤ E) →
      coeffL1 Q ≤ C * E := by
  obtain ⟨C, hC, hbound⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_on_unit_cube n D
  refine ⟨((D + 1) ^ n : ℕ) * C, by positivity, ?_⟩
  intro Q hQ E hE hval
  have h := coeffL1_le_of_coeff_le Q hQ (C * E) (hbound Q hQ E hE hval)
  linarith [h]

end Cube

end

end Submission.Lib.K4QuadraticSheetCore
