import Mathlib

namespace Submission.Obl.k4_quadratic_selector_sweep

open MvPolynomial

/-- Partial differentiation lowers the total-degree bound by one. -/
theorem totalDegree_pderiv_le {σ : Type*} (P : MvPolynomial σ ℝ)
    (i : σ) {d : ℕ} (hP : P.totalDegree ≤ d + 1) :
    (pderiv i P).totalDegree ≤ d := by
  classical
  apply Finset.sup_le
  intro m hm
  have hcoeff : P.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have h := MvPolynomial.mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    exact (mul_ne_zero_iff.mp h).1
  have hdeg := (le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)).trans hP
  have heq : (m + Finsupp.single i 1).sum (fun _ e => e) =
      m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    simp
  rw [heq] at hdeg
  omega

/-- Evaluating a polynomial of degree at most one along an affine line is affine. -/
theorem eval_affine_of_totalDegree_le_one {σ : Type*}
    (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 1) (v w : σ → ℝ) :
    ∃ a c : ℝ, ∀ t : ℝ, eval (fun i => v i + t * w i) P = a * t + c := by
  classical
  have hmon (m : σ →₀ ℕ) (hm : m ∈ P.support) :
      m = 0 ∨ ∃ i, m = Finsupp.single i 1 := by
    have hle := (le_totalDegree hm).trans hP
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · exact Or.inl ((Finsupp.degree_eq_zero_iff m).mp h)
    · exact Or.inr ((Finsupp.sum_eq_one_iff m).mp h)
  have heval (t : ℝ) :
      eval (fun i => v i + t * w i) P =
        t * (eval w P - eval (fun _ => 0) P) + eval v P := by
    conv_lhs => rw [P.as_sum]
    conv_rhs => rw [P.as_sum]
    simp only [map_sum]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rcases hmon m hm with rfl | ⟨i, rfl⟩
    · simp
    · have hi : (Finsupp.single i 1 : σ →₀ ℕ) ≠ 0 := by simp
      simp [eval_monomial, constantCoeff, coeff_monomial, hi]
      ring
  refine ⟨eval w P - eval (fun _ => 0) P, eval v P, fun t => ?_⟩
  rw [heval, mul_comm]

/-- For a quadratic in space-time, the native derivative along a line is affine. -/
theorem quadratic_native_derivative_affine (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b s : EuclideanSpace ℝ (Fin 3)) :
    ∃ a c : ℝ, ∀ t : ℝ,
      eval ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2]
        (pderiv (3 : Fin 4) P) = a * t + c := by
  have hdeg : (pderiv (3 : Fin 4) P).totalDegree ≤ 1 :=
    totalDegree_pderiv_le P 3 hP
  obtain ⟨a, c, hac⟩ := eval_affine_of_totalDegree_le_one
    (pderiv (3 : Fin 4) P) hdeg ![0, b 0, b 1, b 2] ![1, s 0, s 1, s 2]
  refine ⟨a, c, fun t => ?_⟩
  have heq : ![t, (b + t • s) 0, (b + t • s) 1, (b + t • s) 2] =
      (fun i => ![0, b 0, b 1, b 2] i + t * ![1, s 0, s 1, s 2] i) := by
    funext i
    fin_cases i <;> simp
  rw [heq]
  exact hac t

end Submission.Obl.k4_quadratic_selector_sweep
