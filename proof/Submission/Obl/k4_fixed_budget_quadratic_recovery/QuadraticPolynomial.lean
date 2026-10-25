/- Adapted within this LOT tree from o120/x0402, commit 81f800489248f55eaf1c2da13f86ceff0ee98719,
Submission/Obl/k4_unbounded_width_exclusion/QuadraticPolynomial.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MvPolynomial Finset

def quadraticExponent : Fin 6 → (Fin 2 →₀ ℕ) :=
  ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 0 2,
    Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2]

def quadraticPolynomial (c : Fin 6 → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ i, monomial (quadraticExponent i) (c i)

theorem quadraticExponent_degree (i : Fin 6) :
    (quadraticExponent i).sum (fun _ => id) ≤ 2 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  fin_cases i <;> norm_num [quadraticExponent]

theorem quadraticPolynomial_degree (c : Fin 6 → ℝ) :
    (quadraticPolynomial c).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_monomial_le _ _).trans (quadraticExponent_degree i)

theorem eval_quadraticPolynomial (c : Fin 6 → ℝ) (t z : ℝ) :
    eval ![t, z] (quadraticPolynomial c) = quadraticValue c t z := by
  have hev (e : Fin 2 →₀ ℕ) (a : ℝ) :
      eval ![t, z] (monomial e a) = a * (t ^ e 0 * z ^ e 1) := by
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
    simp [Fin.prod_univ_two]
  unfold quadraticPolynomial
  rw [map_sum]
  simp_rw [hev]
  simp [quadraticExponent, Fin.sum_univ_succ, quadraticValue]
  ring

theorem quadraticPolynomial_coeff_bound {c : Fin 6 → ℝ} {H : ℝ}
    (hH : 0 ≤ H) (hc : ∀ i, |c i| ≤ H) (e : Fin 2 →₀ ℕ) :
    |(quadraticPolynomial c).coeff e| ≤ 6 * H := by
  unfold quadraticPolynomial
  rw [coeff_sum]
  calc
    _ ≤ ∑ i, |(monomial (quadraticExponent i) (c i) : MvPolynomial (Fin 2) ℝ).coeff e| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 6, H := by
      apply Finset.sum_le_sum
      intro i _
      rw [coeff_monomial]
      split_ifs
      · exact hc i
      · simpa only [abs_zero] using hH
    _ = _ := by simp

theorem polynomial_eq_of_quadratic_values {P : MvPolynomial (Fin 2) ℝ} {c : Fin 6 → ℝ}
    (h : ∀ t z, eval ![t, z] P = quadraticValue c t z) : P = quadraticPolynomial c := by
  apply MvPolynomial.funext
  intro x
  have hx : (![x 0, x 1] : Fin 2 → ℝ) = x := by ext i; fin_cases i <;> rfl
  rw [← hx, h, eval_quadraticPolynomial]

theorem ScalarCandidate.coeff_bound {N s m ε : ℝ}
    (F : ScalarCandidate N s m ε) (hN : 1 ≤ N) (hε : 0 ≤ ε) (e : Fin 2 →₀ ℕ) :
    |F.P.coeff e| ≤ 240 * (N ^ ε) ^ 5 := by
  obtain ⟨c, hc, hbound⟩ := F.exists_coefficients hN hε
  rw [polynomial_eq_of_quadratic_values hc]
  have h := quadraticPolynomial_coeff_bound (by positivity) hbound e
  convert h using 1
  ring

end Submission.Obl.k4_fixed_budget_quadratic_recovery
