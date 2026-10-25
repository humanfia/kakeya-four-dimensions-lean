/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.LiftedEndpointCoordinates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Fin.Tuple.Basic

open scoped Matrix

namespace Submission.Lib.K4PolynomialNorming

noncomputable def matrixCoordinatesOfRightInverse {m : ℕ}
    (A Ai : Matrix (Fin m) (Fin m) ℝ) (hA : A * Ai = 1) :
    (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (Matrix.toLin'OfInv (M := Ai) (M' := A) (mul_eq_one_comm.mp hA) hA).toContinuousLinearEquiv

theorem matrixCoordinatesOfRightInverse_apply {m : ℕ}
    (A Ai : Matrix (Fin m) (Fin m) ℝ) (hA : A * Ai = 1) (x : Fin m → ℝ) :
    matrixCoordinatesOfRightInverse A Ai hA x = A *ᵥ x := Matrix.toLin'_apply A x

theorem matrixCoordinatesOfRightInverse_symm_apply {m : ℕ}
    (A Ai : Matrix (Fin m) (Fin m) ℝ) (hA : A * Ai = 1) (x : Fin m → ℝ) :
    (matrixCoordinatesOfRightInverse A Ai hA).symm x = Ai *ᵥ x := Matrix.toLin'_apply Ai x

theorem matrixCoordinatesOfRightInverse_det {m : ℕ}
    (A Ai : Matrix (Fin m) (Fin m) ℝ) (hA : A * Ai = 1) :
    LinearMap.det (matrixCoordinatesOfRightInverse A Ai hA).toLinearMap = A.det :=
  LinearMap.det_toLin' A

/-- Split the controls into the first and last direction blocks. -/
noncomputable def finBlockCoordinates (m n : ℕ) :
    (Fin (m + n) → ℝ) ≃L[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
  (show (Fin (m + n) → ℝ) ≃ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) from
    { toFun := fun x => (fun i => x (Fin.castAdd n i),fun j => x (Fin.natAdd m j))
      invFun := fun z => Fin.append z.1 z.2
      left_inv := fun x => Fin.append_castAdd_natAdd
      right_inv := fun z => by ext <;> simp [Fin.append_left, Fin.append_right]
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }).toContinuousLinearEquiv

/-- The full linear endpoint records the physical base and ALL last-block
controls. Its determinant is exactly that of the first direction basis. -/
noncomputable def fullLinearEndpointCoordinates {m : ℕ}
    (A Ai B : Matrix (Fin m) (Fin m) ℝ) (hA : A * Ai = 1) :
    (Fin (m + m) → ℝ) ≃L[ℝ] (Fin (m + m) → ℝ) :=
  (finBlockCoordinates m m).trans
    ((upperBlockCoordinates (matrixCoordinatesOfRightInverse A Ai hA)
      (Matrix.toLin' B).toContinuousLinearMap).trans (finBlockCoordinates m m).symm)

theorem fullLinearEndpointCoordinates_apply {m : ℕ}
    (A Ai B : Matrix (Fin m) (Fin m) ℝ) (hA : A * Ai = 1) (δ : Fin (m + m) → ℝ) :
    fullLinearEndpointCoordinates A Ai B hA δ =
      Fin.append (A *ᵥ (fun i => δ (Fin.castAdd m i)) +
        B *ᵥ (fun i => δ (Fin.natAdd m i))) (fun i => δ (Fin.natAdd m i)) := rfl

theorem fullLinearEndpointCoordinates_symm_apply {m : ℕ}
    (A Ai B : Matrix (Fin m) (Fin m) ℝ) (hA : A * Ai = 1) (z : Fin (m + m) → ℝ) :
    (fullLinearEndpointCoordinates A Ai B hA).symm z =
      Fin.append (Ai *ᵥ ((fun i => z (Fin.castAdd m i)) -
        B *ᵥ (fun i => z (Fin.natAdd m i)))) (fun i => z (Fin.natAdd m i)) := rfl

theorem fullLinearEndpointCoordinates_det {m : ℕ}
    (A Ai B : Matrix (Fin m) (Fin m) ℝ) (hA : A * Ai = 1) :
    LinearMap.det (fullLinearEndpointCoordinates A Ai B hA).toLinearMap = A.det := by
  let e := (finBlockCoordinates m m).symm.toLinearEquiv
  let f := upperBlockCoordinates (matrixCoordinatesOfRightInverse A Ai hA)
    (Matrix.toLin' B).toContinuousLinearMap
  change LinearMap.det (e.toLinearMap ∘ₗ f.toLinearMap ∘ₗ e.symm.toLinearMap) = _
  rw [LinearMap.det_conj, upperBlockCoordinates_det, matrixCoordinatesOfRightInverse_det]

/-- A pure last-block output direction pulls back to precisely the
base-cancelling control vector used by the endpoint minor. -/
theorem fullLinearEndpointCoordinates_inverse_direction {m : ℕ}
    (A Ai B : Matrix (Fin m) (Fin m) ℝ) (hA : A * Ai = 1) (j : Fin m) :
    (fullLinearEndpointCoordinates A Ai B hA).symm
        (Fin.append (0 : Fin m → ℝ) (Pi.single j (1 : ℝ))) =
      Fin.append (fun i => -((Ai * B) i j)) (Pi.single j (1 : ℝ)) := by
  classical
  rw [fullLinearEndpointCoordinates_symm_apply]
  simp only [Fin.append_left, Fin.append_right]
  have hb : B *ᵥ (Pi.single j (1 : ℝ)) = fun a => B a j := by
    ext a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hb]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_neg, Finset.sum_neg_distrib]

end Submission.Lib.K4PolynomialNorming

