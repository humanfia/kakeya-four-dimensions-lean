import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- A common value bound places every normalized test in the same
coefficient ball, to which the original marginal jet count applies. -/
theorem quadratic_difference_coefficients {P Q : Fin 6 → ℝ} {E : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |quadraticValue P t y - quadraticValue Q t y| ≤ E) :
    ∀ i, |P i - Q i| ≤ 8 * E := by
  apply quadratic_coefficients_bound (c := fun i => P i - Q i)
  intro t ht y hy
  have heq : quadraticValue (fun i => P i - Q i) t y =
      quadraticValue P t y - quadraticValue Q t y := by
    unfold quadraticValue
    ring
  rw [heq]
  exact h t ht y hy

/-- Freezing a difference to an offset controls the nonconstant
coefficients at the finer accuracy; the offset affects only the constant. -/
theorem quadratic_coefficients_after_offset {P Q : Fin 6 → ℝ} {offset E : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |quadraticValue P t y - quadraticValue Q t y - offset| ≤ E) :
    |P 0 - Q 0 - offset| ≤ 8 * E ∧ ∀ i, i ≠ 0 → |P i - Q i| ≤ 8 * E := by
  let R : Fin 6 → ℝ := ![P 0 - Q 0 - offset, P 1 - Q 1, P 2 - Q 2,
    P 3 - Q 3, P 4 - Q 4, P 5 - Q 5]
  have hR : ∀ i, |R i| ≤ 8 * E := quadratic_coefficients_bound (by
    intro t ht y hy
    have heq : quadraticValue R t y = quadraticValue P t y - quadraticValue Q t y - offset := by
      simp only [quadraticValue, R, Matrix.cons_val]
      ring
    rw [heq]
    exact h t ht y hy)
  refine ⟨hR 0, ?_⟩
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact hR 1
  · exact hR 2
  · exact hR 3
  · exact hR 4
  · exact hR 5

/-- An occupied common coarse/fine sample bounds the frozen offset in
coarse physical units, without normalizing an intersection mass. -/
theorem frozen_offset_bound {X coarse fine offset Ecoarse Efine variation : ℝ}
    (hc : |X - coarse| ≤ Ecoarse) (hf : |X - fine| ≤ Efine)
    (hv : |fine - coarse - offset| ≤ variation) :
    |offset| ≤ Ecoarse + Efine + variation := by
  have heq : offset = (X - coarse) - (X - fine) - (fine - coarse - offset) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hc hf)) hv)

end Submission.Obl.k4_wide_three_layer_scalar_inputs
