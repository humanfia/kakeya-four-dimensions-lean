import Mathlib

/-!
# Determinants of direction tuples (o013, helper)

Hadamard's inequality for the rows of a real square matrix (from Mathlib's
`Orientation.abs_volumeForm_apply_le`), multiplicativity of the row determinant under a linear map,
and the tuple-by-tuple bound of the finite duality argument:

  `μ * ∑_T |det(e_{i,T_i})| ∏_i c_{i,T_i} ≤ ∏_i ∑_k c_{i,k} ‖A e_{i,k}‖`  whenever `μ ≤ |det A|`.
-/

namespace Submission.Obl.k4_mk_finite_duality

open Module

/-- The determinant of the matrix whose rows are the vectors `v i` (in the standard coordinates)
is the standard basis determinant of the family `v`. -/
theorem det_rows_eq_basis_det {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    Matrix.det (Matrix.of fun i j : Fin n => v i j) =
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v := by
  rw [Module.Basis.det_apply, ← Matrix.det_transpose]
  congr 1

/-- **Hadamard's inequality** for the rows of a real square matrix. -/
theorem abs_det_rows_le_prod_norm {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    |Matrix.det (Matrix.of fun i j : Fin n => v i j)| ≤ ∏ i, ‖v i‖ := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨finrank_euclideanSpace_fin⟩
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) := b.toBasis.orientation
  rw [det_rows_eq_basis_det, ← o.volumeForm_robust' b v]
  exact o.abs_volumeForm_apply_le v

/-- Rows transformed by a linear map `A`: the row determinant is multiplied by `det A`. -/
theorem det_rows_map {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    Matrix.det (Matrix.of fun i j : Fin n => A (v i) j) =
      LinearMap.det A * Matrix.det (Matrix.of fun i j : Fin n => v i j) := by
  rw [det_rows_eq_basis_det, det_rows_eq_basis_det, ← Module.Basis.det_comp]
  rfl

/-- Tuple by tuple, `μ |det(e_{i,T_i})| ≤ |det A| |det(e_{i,T_i})| ≤ ∏_i ‖A e_{i,T_i}‖`
(determinant multiplicativity and Hadamard); multiplying by `∏_i c_{i,T_i}` and summing over the
tuples, the sum factors by finite distributivity. -/
theorem mul_tuple_sum_le {n : ℕ} {N : Fin n → ℕ}
    (e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (c : (i : Fin n) → Fin (N i) → ℝ) (hc : ∀ i k, 0 ≤ c i k) {μ : ℝ}
    (hμ : μ ≤ |LinearMap.det A|) :
    μ * ∑ T : ((i : Fin n) → Fin (N i)),
        |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, c i (T i)
      ≤ ∏ i : Fin n, ∑ k : Fin (N i), c i k * ‖A (e i k)‖ := by
  have hF : 0 ≤ ∑ T : ((i : Fin n) → Fin (N i)),
      |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, c i (T i) :=
    Finset.sum_nonneg fun T _ =>
      mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun i _ => hc i (T i))
  calc μ * ∑ T : ((i : Fin n) → Fin (N i)),
        |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, c i (T i)
      ≤ |LinearMap.det A| * ∑ T : ((i : Fin n) → Fin (N i)),
        |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, c i (T i) :=
        mul_le_mul_of_nonneg_right hμ hF
    _ = ∑ T : ((i : Fin n) → Fin (N i)),
        |Matrix.det (Matrix.of fun i j : Fin n => A (e i (T i)) j)| * ∏ i : Fin n, c i (T i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [det_rows_map A (fun i => e i (T i)), abs_mul, mul_assoc]
    _ ≤ ∑ T : ((i : Fin n) → Fin (N i)),
        (∏ i : Fin n, ‖A (e i (T i))‖) * ∏ i : Fin n, c i (T i) :=
        Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_right
          (abs_det_rows_le_prod_norm fun i => A (e i (T i)))
          (Finset.prod_nonneg fun i _ => hc i (T i))
    _ = ∑ T : ((i : Fin n) → Fin (N i)), ∏ i : Fin n, c i (T i) * ‖A (e i (T i))‖ := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => mul_comm _ _
    _ = ∏ i : Fin n, ∑ k : Fin (N i), c i k * ‖A (e i k)‖ :=
        (Fintype.prod_sum fun i k => c i k * ‖A (e i k)‖).symm

end Submission.Obl.k4_mk_finite_duality
