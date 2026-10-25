import Mathlib

/-!
The coordinate-volume formulas below are adapted from original proofs by
session x0138 in this LOT tree, obligation o046, commit bd54619,
Submission/Obl/k4_adapted_oscillation_tests/Affine.lean.
-/

namespace Submission.Obl.k4_affine_cube_directional_poincare

open MeasureTheory Set

/-- The coordinate cube viewed in Euclidean space. -/
def euclideanUnitCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1

lemma isCompact_euclideanUnitCube (n : ℕ) : IsCompact (euclideanUnitCube n) :=
  isCompact_Icc.image (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.continuous

lemma integral_euclideanUnitCube {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x in euclideanUnitCube n, g x =
      ∫ t in Set.Icc (0 : Fin n → ℝ) 1, g (WithLp.toLp 2 t) :=
  (PiLp.volume_preserving_toLp (Fin n)).setIntegral_image_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding g _

/-- Change variables from an affine Euclidean cube to the coordinate unit cube. -/
theorem integral_affine_coordinateCube {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x in (fun t : Fin n → ℝ => a + L (WithLp.toLp 2 t)) ''
        Set.Icc (0 : Fin n → ℝ) 1, g x) =
      |LinearMap.det (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| *
        ∫ t in Set.Icc (0 : Fin n → ℝ) 1, g (a + L (WithLp.toLp 2 t)) := by
  have hd : ∀ x ∈ euclideanUnitCube n,
      HasFDerivWithinAt (fun x => a + L x)
        (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (euclideanUnitCube n) x :=
    fun x _ => L.hasFDerivAt.const_add a |>.hasFDerivWithinAt
  have hi : Set.InjOn (fun x => a + L x) (euclideanUnitCube n) := by
    intro x _ y _ h
    exact L.injective (add_left_cancel h)
  have himage : (fun t : Fin n → ℝ => a + L (WithLp.toLp 2 t)) ''
      Set.Icc (0 : Fin n → ℝ) 1 = (fun x => a + L x) '' euclideanUnitCube n := by
    rw [euclideanUnitCube, Set.image_image]
  rw [himage, integral_image_eq_integral_abs_det_fderiv_smul volume
    (isCompact_euclideanUnitCube n).measurableSet hd hi]
  simp only [smul_eq_mul]
  rw [integral_const_mul, integral_euclideanUnitCube]
  rfl

/-- The same Jacobian multiplies both sides of the coordinate Poincare estimate. -/
theorem ambient_poincare_of_coordinate_bound {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (a : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hbound :
      (∫ t in Set.Icc (0 : Fin n → ℝ) 1, |f (a + L (WithLp.toLp 2 t))|) -
        |∫ t in Set.Icc (0 : Fin n → ℝ) 1, f (a + L (WithLp.toLp 2 t))| ≤
      ∑ i : Fin n, ∫ t in Set.Icc (0 : Fin n → ℝ) 1,
        ‖fderiv ℝ f (a + L (WithLp.toLp 2 t)) (L (WithLp.toLp 2 (Pi.single i 1)))‖) :
    let Q := (fun t : Fin n → ℝ => a + L (WithLp.toLp 2 t)) ''
      Set.Icc (0 : Fin n → ℝ) 1
    (∫ x in Q, |f x|) - |∫ x in Q, f x| ≤
      ∑ i : Fin n, ∫ x in Q,
        ‖fderiv ℝ f x (L (WithLp.toLp 2 (Pi.single i 1)))‖ := by
  dsimp only
  simp_rw [integral_affine_coordinateCube]
  rw [abs_mul, abs_abs, ← mul_sub, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)

end Submission.Obl.k4_affine_cube_directional_poincare
