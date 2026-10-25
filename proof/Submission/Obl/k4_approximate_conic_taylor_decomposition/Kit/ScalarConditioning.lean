/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/ScalarConditioning.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/ScalarConditioning.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

noncomputable def offDiagonalRemainder (M : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  ∑ k ∈ (Finset.univ : Finset (Fin 3)).erase j, M j k * v k

theorem mulVec_eq_diagonal_add_remainder (M : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 3 → ℝ) (j : Fin 3) :
    Matrix.mulVec M v j = M j j * v j + offDiagonalRemainder M v j := by
  exact (Finset.add_sum_erase Finset.univ (fun k => M j k * v k) (Finset.mem_univ j)).symm

theorem offDiagonalRemainder_abs_le (M : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 3 → ℝ) (A ε : ℝ) (_hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hv : ∀ j, |v j| ≤ A) (hM : ∀ i j, i ≠ j → |M i j| ≤ ε) (j : Fin 3) :
    |offDiagonalRemainder M v j| ≤ 2 * A * ε := by
  unfold offDiagonalRemainder
  calc
    _ ≤ ∑ k ∈ (Finset.univ : Finset (Fin 3)).erase j, |M j k * v k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ (Finset.univ : Finset (Fin 3)).erase j, ε * A := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (hM j k (Finset.mem_erase.mp hk).1.symm) (hv k) (abs_nonneg _) hε
    _ = _ := by simp; ring

/-- Approximate eigenvector tests in a projective frame determine a scalar
matrix, with a polynomial coefficient bound. -/
theorem matrix_near_scalar_of_projective_frame_tests
    (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) (A ε : ℝ)
    (hA : 1 ≤ A) (hε : 0 ≤ ε) (hv : ∀ j, |v j| ≤ A)
    (hlow : ∀ j, 1 ≤ A * |v j|)
    (hM : ∀ i j, i ≠ j → |M i j| ≤ ε)
    (hcross : ∀ j k, |v k * Matrix.mulVec M v j - v j * Matrix.mulVec M v k| ≤ ε) :
    ∀ i j, |M i j - (if i = j then M 0 0 else 0)| ≤ 5 * A ^ 4 * ε := by
  have hA0 : 0 ≤ A := by linarith
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hA4 : 1 ≤ A ^ 4 := by nlinarith [sq_nonneg (A ^ 2 - 1)]
  have hε2 : ε ≤ A ^ 2 * ε := by nlinarith [mul_nonneg (sub_nonneg.mpr hA2) hε]
  have hε4 : ε ≤ 5 * A ^ 4 * ε := by nlinarith [mul_nonneg (sub_nonneg.mpr hA4) hε]
  have hR (j : Fin 3) := offDiagonalRemainder_abs_le M v A ε hA0 hε hv hM j
  have hdiag (j k : Fin 3) : |M j j - M k k| ≤ 5 * A ^ 4 * ε := by
    have heq : v j * v k * (M j j - M k k) =
        (v k * Matrix.mulVec M v j - v j * Matrix.mulVec M v k) -
          v k * offDiagonalRemainder M v j + v j * offDiagonalRemainder M v k := by
      rw [mulVec_eq_diagonal_add_remainder, mulVec_eq_diagonal_add_remainder]
      ring
    have hprod : |v j * v k| * |M j j - M k k| ≤ 5 * A ^ 2 * ε := by
      rw [← abs_mul, heq]
      calc
        _ ≤ (|v k * Matrix.mulVec M v j - v j * Matrix.mulVec M v k| +
            |v k * offDiagonalRemainder M v j|) + |v j * offDiagonalRemainder M v k| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ (ε + A * (2 * A * ε)) + A * (2 * A * ε) := by
          simp only [abs_mul]
          exact add_le_add (add_le_add (hcross j k)
            (mul_le_mul (hv k) (hR j) (abs_nonneg _) hA0))
            (mul_le_mul (hv j) (hR k) (abs_nonneg _) hA0)
        _ ≤ _ := by nlinarith
    have hden : 1 ≤ A ^ 2 * |v j * v k| := by
      calc
        1 = 1 * 1 := by ring
        _ ≤ (A * |v j|) * (A * |v k|) :=
          mul_le_mul (hlow j) (hlow k) (by norm_num) (by positivity)
        _ = _ := by rw [abs_mul]; ring
    calc
      |M j j - M k k| ≤ (A ^ 2 * |v j * v k|) * |M j j - M k k| :=
        le_mul_of_one_le_left (abs_nonneg _) hden
      _ = A ^ 2 * (|v j * v k| * |M j j - M k k|) := by ring
      _ ≤ A ^ 2 * (5 * A ^ 2 * ε) := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
      _ = _ := by ring
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using hdiag i 0
  · simpa [hij] using (hM i j hij).trans hε4

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
