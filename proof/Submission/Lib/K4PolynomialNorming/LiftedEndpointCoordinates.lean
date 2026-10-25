/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.LinearEndpointCoordinates

namespace Submission.Lib.K4PolynomialNorming

/-- Add the unused controls to the linear target while retaining their
values. The off-diagonal block changes no determinant. -/
noncomputable def upperBlockCoordinates {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E ≃L[ℝ] E) (C : F →L[ℝ] E) : (E × F) ≃L[ℝ] (E × F) :=
  ((LinearEquiv.prodComm ℝ E F).trans
    (((LinearEquiv.refl ℝ F).skewProd L.toLinearEquiv C.toLinearMap).trans
      (LinearEquiv.prodComm ℝ F E))).toContinuousLinearEquiv

theorem upperBlockCoordinates_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E ≃L[ℝ] E) (C : F →L[ℝ] E) (x : E × F) :
    upperBlockCoordinates L C x = (L x.1 + C x.2,x.2) := rfl

theorem upperBlockCoordinates_symm_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E ≃L[ℝ] E) (C : F →L[ℝ] E) (x : E × F) :
    (upperBlockCoordinates L C).symm x = (L.symm (x.1 - C x.2),x.2) := rfl

theorem upperBlockCoordinates_det {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E ≃L[ℝ] E) (C : F →L[ℝ] E) :
    LinearMap.det (upperBlockCoordinates L C).toLinearMap = LinearMap.det L.toLinearMap := by
  let f := (LinearEquiv.refl ℝ F).skewProd L.toLinearEquiv C.toLinearMap
  let s := LinearEquiv.prodComm ℝ F E
  change LinearMap.det (s.toLinearMap ∘ₗ f.toLinearMap ∘ₗ s.symm.toLinearMap) = _
  rw [LinearMap.det_conj, linearEquiv_skewProd_det]
  simp

/-- Coordinates for the full endpoint, with every unused control preserved
as a linear coordinate and one selected extra duration at the end. -/
noncomputable def liftedBaseEndpointCoordinates {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E ≃L[ℝ] E) (C : F →L[ℝ] E) (w : E) :
    ((E × F) × ℝ) ≃L[ℝ] ((E × F) × ℝ) :=
  linearBaseEndpointCoordinates (upperBlockCoordinates L C) (w,0)

theorem liftedBaseEndpointCoordinates_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E ≃L[ℝ] E) (C : F →L[ℝ] E) (w x : E) (s : F) (t : ℝ) :
    liftedBaseEndpointCoordinates L C w ((x,s),t) = ((L x + C s + t • w,s),t) := by
  simp [liftedBaseEndpointCoordinates, linearBaseEndpointCoordinates_apply,
    upperBlockCoordinates_apply]

theorem liftedBaseEndpointCoordinates_kernel_direction {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E ≃L[ℝ] E) (C : F →L[ℝ] E) (w : E) :
    (liftedBaseEndpointCoordinates L C w).symm (0,1) = ((-L.symm w,0),1) := by
  simp [liftedBaseEndpointCoordinates, linearBaseEndpointCoordinates_kernel_direction,
    upperBlockCoordinates_symm_apply]

theorem liftedBaseEndpointCoordinates_det {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E ≃L[ℝ] E) (C : F →L[ℝ] E) (w : E) :
    LinearMap.det (liftedBaseEndpointCoordinates L C w).toLinearMap =
      LinearMap.det L.toLinearMap := by
  rw [liftedBaseEndpointCoordinates, linearBaseEndpointCoordinates_det, upperBlockCoordinates_det]

end Submission.Lib.K4PolynomialNorming

