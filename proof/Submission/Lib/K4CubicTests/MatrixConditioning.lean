/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

namespace Submission.Lib.K4CubicTests

/-- A determinant bound from coordinate bounds in dimension three. -/
theorem matrix_det_three_abs_le (M : Matrix (Fin 3) (Fin 3) ℝ)
    (A : ℝ) (hA : 0 ≤ A) (hM : ∀ i j, |M i j| ≤ A) :
    |M.det| ≤ 6 * A ^ 3 := by
  have hterm (a b c d e f : Fin 3) : |M a b * M c d * M e f| ≤ A ^ 3 := by
    simp only [abs_mul]
    calc
      _ ≤ A * A * A := mul_le_mul
        (mul_le_mul (hM a b) (hM c d) (abs_nonneg _) hA) (hM e f)
        (abs_nonneg _) (mul_nonneg hA hA)
      _ = _ := by ring
  rcases abs_le.mp (hterm 0 0 1 1 2 2) with ⟨h1l, h1u⟩
  rcases abs_le.mp (hterm 0 0 1 2 2 1) with ⟨h2l, h2u⟩
  rcases abs_le.mp (hterm 0 1 1 0 2 2) with ⟨h3l, h3u⟩
  rcases abs_le.mp (hterm 0 1 1 2 2 0) with ⟨h4l, h4u⟩
  rcases abs_le.mp (hterm 0 2 1 0 2 1) with ⟨h5l, h5u⟩
  rcases abs_le.mp (hterm 0 2 1 1 2 0) with ⟨h6l, h6u⟩
  rw [Matrix.det_fin_three]
  apply abs_le.mpr
  constructor <;> linarith

/-- A coordinate bound for the adjugate in dimension three. -/
theorem matrix_adjugate_three_abs_le (M : Matrix (Fin 3) (Fin 3) ℝ)
    (A : ℝ) (hA : 0 ≤ A) (hM : ∀ i j, |M i j| ≤ A) (i j : Fin 3) :
    |M.adjugate i j| ≤ 2 * A ^ 2 := by
  have hminor (a b c d e f g h : Fin 3) :
      |M a b * M c d - M e f * M g h| ≤ 2 * A ^ 2 := by
    calc
      _ ≤ |M a b * M c d| + |M e f * M g h| := abs_sub _ _
      _ = |M a b| * |M c d| + |M e f| * |M g h| := by rw [abs_mul, abs_mul]
      _ ≤ A * A + A * A := add_le_add
        (mul_le_mul (hM a b) (hM c d) (abs_nonneg _) hA)
        (mul_le_mul (hM e f) (hM g h) (abs_nonneg _) hA)
      _ = _ := by ring
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, neg_add_eq_sub] <;> exact hminor _ _ _ _ _ _ _ _

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
      mul_le_mul hinv (matrix_adjugate_three_abs_le M A hA hM i j)
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

end Submission.Lib.K4CubicTests
