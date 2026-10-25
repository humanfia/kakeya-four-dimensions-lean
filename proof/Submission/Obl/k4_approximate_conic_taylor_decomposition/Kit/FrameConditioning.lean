/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/FrameConditioning.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/FrameConditioning.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.MatrixConditioning
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.CubicTensor

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

/-- The basis vectors arranged as the rows of a matrix. -/
noncomputable def basisRows (b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (fun i j => b i j)

/-- Cramer's identity for coordinates in an arbitrary three-dimensional basis. -/
theorem basis_repr_mul_det_eq_updateRow (b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ))
    (v : Fin 3 → ℝ) (i : Fin 3) :
    b.repr v i * (basisRows b).det = ((basisRows b).updateRow i v).det := by
  calc
    _ = ((basisRows b).updateRow i (∑ j : Fin 3, b.repr v j • (basisRows b) j)).det :=
      (Matrix.det_updateRow_sum (basisRows b) i (b.repr v)).symm
    _ = _ := by
      apply congrArg (fun w => ((basisRows b).updateRow i w).det)
      exact b.sum_repr v

/-- Upper bounds for all coordinates in a well-conditioned basis. -/
theorem basis_repr_abs_le_of_det (b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ))
    (A B κ : ℝ) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hb : ∀ i j, |b i j| ≤ A) (hdet : κ ≤ |(basisRows b).det|)
    (v : Fin 3 → ℝ) (hv : ∀ j, |v j| ≤ B) (i : Fin 3) :
    |b.repr v i| ≤ 6 * A ^ 2 * B / κ := by
  let M := (basisRows b).transpose
  have hMdet : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    exact abs_pos.mp (hκ.trans_le (by simpa [M] using hdet))
  have hexp : Matrix.mulVec M (fun j => b.repr v j) = v := by
    funext k
    simpa [M, Matrix.mulVec, dotProduct, basisRows, smul_eq_mul, mul_comm] using congrFun (b.sum_repr v) k
  have hcoord : (fun j => b.repr v j) = Matrix.mulVec M⁻¹ v := by
    have h := congrArg (Matrix.mulVec M⁻¹) hexp
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hMdet, Matrix.one_mulVec] at h
    exact h
  rw [congrFun hcoord i]
  apply matrix_inverse_three_mulVec_abs_le M A B κ hA hκ
  · intro j k
    exact hb k j
  · simpa [M] using hdet
  · exact hv

/-- A determinant lower bound for replacing one basis vector bounds its
coordinate away from zero, with an explicit polynomial loss. -/
theorem basis_repr_abs_ge_of_replaced_det (b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ))
    (A κ : ℝ) (hA : 0 < A) (hb : ∀ i j, |b i j| ≤ A)
    (v : Fin 3 → ℝ) (i : Fin 3)
    (hdet : κ ≤ |((basisRows b).updateRow i v).det|) :
    κ ≤ |b.repr v i| * (6 * A ^ 3) := by
  calc
    κ ≤ |((basisRows b).updateRow i v).det| := hdet
    _ = |b.repr v i| * |(basisRows b).det| := by
      rw [← basis_repr_mul_det_eq_updateRow, abs_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (matrix_det_three_abs_le (basisRows b) A hA.le hb) (abs_nonneg _)

/-- Polynomial conditioning for the cubic two-copy tests directly from
coordinate and determinant bounds on a projective frame. -/
theorem cubic_coefficients_le_of_frame_determinants
    (b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ))
    (T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (h01 : ∀ x y z, T x y z = T y x z)
    (h12 : ∀ x y z, T x y z = T x z y)
    (v : Fin 3 → ℝ) (A κ ε : ℝ) (hA : 0 < A) (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hb : ∀ i j, |b i j| ≤ A) (hvcoord : ∀ j, |v j| ≤ A)
    (hdet : κ ≤ |(basisRows b).det|)
    (hdet1 : κ ≤ |((basisRows b).updateRow 1 v).det|)
    (hdet2 : κ ≤ |((basisRows b).updateRow 2 v).det|)
    (hB : ∀ i j : Fin 3, |T (b i) (b i) (b j)| ≤ ε)
    (hv : |T v v (b 0)| ≤ ε) :
    ∀ i j k : Fin 3, |T (b i) (b j) (b k)| ≤ 4 * (6 * A ^ 3 / κ) ^ 4 * ε := by
  have hsize : κ ≤ 6 * A ^ 3 := hdet.trans (matrix_det_three_abs_le (basisRows b) A hA.le hb)
  have hlarge : 1 ≤ 6 * A ^ 3 / κ := (le_div_iff₀ hκ).mpr (by simpa using hsize)
  have hrepr (i : Fin 3) : |b.repr v i| ≤ 6 * A ^ 3 / κ := by
    convert basis_repr_abs_le_of_det b A A κ hA.le hκ hb hdet v hvcoord i using 1 <;> ring
  have hlow (i : Fin 3) (hi : κ ≤ |((basisRows b).updateRow i v).det|) :
      1 ≤ (6 * A ^ 3 / κ) * |b.repr v i| := by
    have h := basis_repr_abs_ge_of_replaced_det b A κ hA hb v i hi
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hκ).mpr
    simpa [mul_comm] using h
  exact cubic_coefficients_le_of_two_copy_tests b T h01 h12 v _ ε hlarge hε hrepr
    (hlow 1 hdet1) (hlow 2 hdet2) hB hv

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
