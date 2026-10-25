import Mathlib

/-!
# A polynomial of total degree at most two in `(t, w)` as a quadratic in `w`

`P(t, w) = γ w ^ 2 + α(t) w + β(t)` with `γ` constant, `deg α ≤ 1` and `deg β ≤ 2`.
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Polynomial Finset

noncomputable section

theorem exists_quadratic_in_last (P : MvPolynomial (Fin 2) ℂ) (hP : P.totalDegree ≤ 2) :
    ∃ γ : ℂ, ∃ α β : ℂ[X], α.natDegree ≤ 1 ∧ β.natDegree ≤ 2 ∧
      ∀ t w : ℂ, MvPolynomial.eval (Fin.snoc (fun _ : Fin 1 => t) w) P =
        γ * w ^ 2 + α.eval t * w + β.eval t := by
  classical
  have hdeg : ∀ μ ∈ P.support, μ 0 + μ 1 ≤ 2 := by
    intro μ hμ
    have := MvPolynomial.le_totalDegree hμ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
    omega
  refine ⟨∑ μ ∈ P.support.filter (fun μ => μ 1 = 2), P.coeff μ,
    ∑ μ ∈ P.support.filter (fun μ => μ 1 = 1), C (P.coeff μ) * X ^ (μ 0),
    ∑ μ ∈ P.support.filter (fun μ => μ 1 = 0), C (P.coeff μ) * X ^ (μ 0), ?_, ?_, ?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro μ hμ
    obtain ⟨hμs, hμ1⟩ := mem_filter.mp hμ
    have := hdeg μ hμs
    exact natDegree_C_mul_X_pow_le _ _ |>.trans (by omega)
  · apply natDegree_sum_le_of_forall_le
    intro μ hμ
    obtain ⟨hμs, hμ1⟩ := mem_filter.mp hμ
    have := hdeg μ hμs
    exact natDegree_C_mul_X_pow_le _ _ |>.trans (by omega)
  · intro t w
    rw [MvPolynomial.eval_eq']
    have hprod : ∀ d : Fin 2 →₀ ℕ,
        ∏ i, (Fin.snoc (fun _ : Fin 1 => t) w : Fin 2 → ℂ) i ^ d i = t ^ d 0 * w ^ d 1 := by
      intro d
      rw [Fin.prod_univ_two]
      rfl
    simp only [hprod]
    rw [← sum_fiberwise_of_maps_to (s := P.support) (t := range 3) (g := fun μ => μ 1)
      (fun μ hμ => mem_range.mpr (by have := hdeg μ hμ; omega))]
    simp only [sum_range_succ, sum_range_zero, zero_add]
    rw [eval_finsetSum, eval_finsetSum, sum_mul, sum_mul]
    have h2 : ∀ μ ∈ P.support.filter (fun μ => μ 1 = 2),
        P.coeff μ * (t ^ μ 0 * w ^ μ 1) = P.coeff μ * w ^ 2 := by
      intro μ hμ
      obtain ⟨hμs, hμ1⟩ := mem_filter.mp hμ
      have := hdeg μ hμs
      have h0 : μ 0 = 0 := by omega
      rw [h0, hμ1, pow_zero, one_mul]
    have h1 : ∀ μ ∈ P.support.filter (fun μ => μ 1 = 1),
        P.coeff μ * (t ^ μ 0 * w ^ μ 1) = (C (P.coeff μ) * X ^ μ 0).eval t * w := by
      intro μ hμ
      rw [(mem_filter.mp hμ).2, eval_mul, eval_C, eval_pow, eval_X, pow_one]
      ring
    have h0 : ∀ μ ∈ P.support.filter (fun μ => μ 1 = 0),
        P.coeff μ * (t ^ μ 0 * w ^ μ 1) = (C (P.coeff μ) * X ^ μ 0).eval t := by
      intro μ hμ
      rw [(mem_filter.mp hμ).2, eval_mul, eval_C, eval_pow, eval_X, pow_zero, mul_one]
    rw [sum_congr rfl h2, sum_congr rfl h1, sum_congr rfl h0, ← sum_mul]
    ring

end

end Submission.Obl.k4_quadratic_sheet_continuation
