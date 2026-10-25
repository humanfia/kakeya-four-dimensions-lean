import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

/-- Summed posterior palette weights bound a residual list. The original
coarse palette mass is used on both sides and cancels only at the end. -/
theorem palette_weighted_list_count {A V : Type*} [DecidableEq A] [DecidableEq V]
    (states : Finset A) (velocities : Finset V) (weight : V → ℝ)
    (compatible : A → V → Prop) [DecidableRel compatible]
    {P C K : ℝ} (hP : 0 < P) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hw : ∀ j ∈ velocities, 0 ≤ weight j)
    (hmass : ∑ j ∈ velocities, weight j ≤ P)
    (hrow : ∀ a ∈ states, P ≤ C *
      ∑ j ∈ Finset.bipartiteAbove compatible velocities a, weight j)
    (hcolumn : ∀ j ∈ velocities,
      ((Finset.bipartiteBelow compatible states j).card : ℝ) ≤ K) :
    (states.card : ℝ) ≤ C * K := by
  have hcount : (states.card : ℝ) * P ≤ C * K * P := by
    calc
      _ = ∑ _a ∈ states, P := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ states, C * ∑ j ∈ Finset.bipartiteAbove compatible velocities a, weight j :=
        Finset.sum_le_sum hrow
      _ = C * ∑ a ∈ states, ∑ j ∈ Finset.bipartiteAbove compatible velocities a, weight j := by
        rw [Finset.mul_sum]
      _ = C * ∑ j ∈ velocities, ∑ _a ∈ Finset.bipartiteBelow compatible states j, weight j := by
        rw [Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow compatible (fun _ j => weight j)]
      _ = C * ∑ j ∈ velocities, ((Finset.bipartiteBelow compatible states j).card : ℝ) * weight j := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C * ∑ j ∈ velocities, K * weight j := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hcolumn j hj) (hw j hj))
      _ = C * (K * ∑ j ∈ velocities, weight j) := by simp only [Finset.mul_sum]
      _ ≤ C * (K * P) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass hK) hC
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ hP).mp hcount

end Submission.Obl.k4_scalar_grid_polynomial_qualification
