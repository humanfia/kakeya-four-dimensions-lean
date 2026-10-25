/-
Adapted from: here:root
Original proofs by session x0001, root branch x0001-cubiclib, commit f6ada26.
Source: Submission/Lib/K4CubicTests/MatrixConditioning.lean.
This helper has not entered lib; only the cubic two-copy argument is used here.
-/
import Submission.Obl.k4_real_conic_restoration.Basic

namespace Submission.Obl.k4_seven_direction_third_derivative_bound

/-- A coordinate bound for a matrix inverse from a determinant lower bound. -/
theorem matrix_inverse_three_abs_le (M : Matrix (Fin 3) (Fin 3) ℝ)
    (A κ : ℝ) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hM : ∀ i j, |M i j| ≤ A) (hdet : κ ≤ |M.det|) (i j : Fin 3) :
    |M⁻¹ i j| ≤ 2 * A ^ 2 / κ := by
  have hinv : |M.det|⁻¹ ≤ κ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hκ hdet
  rw [Matrix.inv_def]
  change |(Ring.inverse M.det) * M.adjugate i j| ≤ _
  simp only [Ring.inverse_eq_inv, abs_mul, abs_inv]
  calc
    _ ≤ κ⁻¹ * (2 * A ^ 2) :=
      mul_le_mul hinv (Submission.Obl.k4_real_conic_restoration.adjugate_bound hM i j)
        (abs_nonneg _) (inv_nonneg.mpr hκ.le)
    _ = _ := by ring

/-- A coordinate bound for applying an inverse to a bounded vector. -/
theorem matrix_inverse_three_mulVec_abs_le (M : Matrix (Fin 3) (Fin 3) ℝ)
    (A B κ : ℝ) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hM : ∀ i j, |M i j| ≤ A) (hdet : κ ≤ |M.det|)
    (v : Fin 3 → ℝ) (hv : ∀ j, |v j| ≤ B) (i : Fin 3) :
    |(Matrix.mulVec M⁻¹ v) i| ≤ 6 * A ^ 2 * B / κ := by
  rw [Matrix.mulVec, dotProduct]
  calc
    |∑ j : Fin 3, M⁻¹ i j * v j| ≤ ∑ j : Fin 3, |M⁻¹ i j * v j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, (2 * A ^ 2 / κ) * B := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (matrix_inverse_three_abs_le M A κ hA hκ hM hdet i j) (hv j)
        (abs_nonneg _) (by positivity)
    _ = _ := by simp; ring

end Submission.Obl.k4_seven_direction_third_derivative_bound
