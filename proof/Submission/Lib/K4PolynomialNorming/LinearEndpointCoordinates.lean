/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.NormNum

open scoped LinearMap

namespace Submission.Lib.K4PolynomialNorming

/-- A block-triangular linear equivalence has the product of the two
diagonal determinants, independently of its off-diagonal block. -/
theorem linearEquiv_skewProd_det {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (L : E ≃ₗ[ℝ] E) (M : F ≃ₗ[ℝ] F) (A : E →ₗ[ℝ] F) :
    LinearMap.det (L.skewProd M A).toLinearMap =
      LinearMap.det L.toLinearMap * LinearMap.det M.toLinearMap := by
  classical
  let b := Module.finBasis ℝ E
  let c := Module.finBasis ℝ F
  have hmatrix : LinearMap.toMatrix (b.prod c) (b.prod c) (L.skewProd M A).toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix b b L.toLinearMap) 0
        (LinearMap.toMatrix b c A) (LinearMap.toMatrix c c M.toLinearMap) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix]
  rw [← LinearMap.det_toMatrix (b.prod c), hmatrix, Matrix.det_fromBlocks_zero₁₂,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

/-- Invertible base coordinates, retaining the extra duration unchanged. -/
noncomputable def linearBaseEndpointCoordinates {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : E ≃L[ℝ] E) (w : E) : (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  ((LinearEquiv.prodComm ℝ E ℝ).trans
    (((LinearEquiv.refl ℝ ℝ).skewProd L.toLinearEquiv
      ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight w)).trans
        (LinearEquiv.prodComm ℝ ℝ E))).toContinuousLinearEquiv

theorem linearBaseEndpointCoordinates_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : E ≃L[ℝ] E) (w : E) (x : E × ℝ) :
    linearBaseEndpointCoordinates L w x = (L x.1 + x.2 • w, x.2) := rfl

theorem linearBaseEndpointCoordinates_symm_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : E ≃L[ℝ] E) (w : E) (x : E × ℝ) :
    (linearBaseEndpointCoordinates L w).symm x = (L.symm (x.1 - x.2 • w), x.2) := rfl

theorem linearBaseEndpointCoordinates_kernel_direction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : E ≃L[ℝ] E) (w : E) :
    (linearBaseEndpointCoordinates L w).symm (0,1) = (-L.symm w,1) := by
  rw [linearBaseEndpointCoordinates_symm_apply]
  simp

theorem linearBaseEndpointCoordinates_det {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : E ≃L[ℝ] E) (w : E) :
    LinearMap.det (linearBaseEndpointCoordinates L w).toLinearMap =
      LinearMap.det L.toLinearMap := by
  let A := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight w
  let f := (LinearEquiv.refl ℝ ℝ).skewProd L.toLinearEquiv A
  let s := LinearEquiv.prodComm ℝ ℝ E
  change LinearMap.det (s.toLinearMap ∘ₗ f.toLinearMap ∘ₗ s.symm.toLinearMap) = _
  rw [LinearMap.det_conj, linearEquiv_skewProd_det]
  simp

end Submission.Lib.K4PolynomialNorming
