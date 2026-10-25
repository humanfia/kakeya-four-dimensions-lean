/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/WedgeConditioning.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/WedgeConditioning.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

/-- A coordinate of the exterior product, written without exterior-algebra
infrastructure so its conditioning constants are explicit. -/
def crossCoordinate (u v : Fin 3 → ℝ) (j k : Fin 3) : ℝ :=
  u k * v j - u j * v k

private theorem abs_sum_three_le (f : Fin 3 → ℝ) (B : ℝ) (hf : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 3 * B := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B := Finset.sum_le_sum fun i _ => hf i
    _ = _ := by simp

private theorem abs_double_sum_three_le (f : Fin 3 → Fin 3 → ℝ)
    (B : ℝ) (hf : ∀ i j, |f i j| ≤ B) : |∑ i, ∑ j, f i j| ≤ 9 * B := by
  have hinner (i : Fin 3) := abs_sum_three_le (f i) B (hf i)
  convert abs_sum_three_le (fun i => ∑ j, f i j) (3 * B) hinner using 1 <;> ring

/-- The exterior-square formula for a matrix acting on two vectors. -/
theorem crossCoordinate_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ)
    (u v : Fin 3 → ℝ) (j k : Fin 3) :
    crossCoordinate (Matrix.mulVec M u) (Matrix.mulVec M v) j k =
      ∑ a : Fin 3, ∑ b : Fin 3, M k a * M j b * crossCoordinate u v b a := by
  simp only [crossCoordinate, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- A matrix changes the pairwise proportionality tests by at most a
quadratic coefficient loss. -/
theorem crossCoordinate_mulVec_abs_le (M : Matrix (Fin 3) (Fin 3) ℝ)
    (u v : Fin 3 → ℝ) (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hM : ∀ i j, |M i j| ≤ A) (huv : ∀ j k, |crossCoordinate u v j k| ≤ ε)
    (j k : Fin 3) :
    |crossCoordinate (Matrix.mulVec M u) (Matrix.mulVec M v) j k| ≤ 9 * A ^ 2 * ε := by
  rw [crossCoordinate_mulVec]
  have hterm (a b : Fin 3) : |M k a * M j b * crossCoordinate u v b a| ≤ A ^ 2 * ε := by
    simp only [abs_mul]
    calc
      _ ≤ (A * A) * ε := mul_le_mul
        (mul_le_mul (hM k a) (hM j b) (abs_nonneg _) hA) (huv b a)
        (abs_nonneg _) (mul_nonneg hA hA)
      _ = _ := by ring
  convert abs_double_sum_three_le _ (A ^ 2 * ε) hterm using 1 <;> ring

/-- A coefficient bound for multiplying two three-dimensional matrices. -/
theorem matrix_mul_three_entry_abs_le (M N : Matrix (Fin 3) (Fin 3) ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hM : ∀ i j, |M i j| ≤ A) (hN : ∀ i j, |N i j| ≤ B)
    (i j : Fin 3) : |(M * N) i j| ≤ 3 * A * B := by
  rw [Matrix.mul_apply]
  have hterm (k : Fin 3) : |M i k * N k j| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (hM i k) (hN k j) (abs_nonneg _) hA
  convert abs_sum_three_le _ (A * B) hterm using 1 <;> ring

/-- A coefficient bound for applying a three-dimensional matrix. -/
theorem matrix_mulVec_three_abs_le (M : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 3 → ℝ) (A B : ℝ) (hA : 0 ≤ A)
    (hM : ∀ i j, |M i j| ≤ A) (hv : ∀ j, |v j| ≤ B) (i : Fin 3) :
    |Matrix.mulVec M v i| ≤ 3 * A * B := by
  rw [Matrix.mulVec, dotProduct]
  have hterm (k : Fin 3) : |M i k * v k| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (hM i k) (hv k) (abs_nonneg _) hA
  convert abs_sum_three_le _ (A * B) hterm using 1 <;> ring

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
