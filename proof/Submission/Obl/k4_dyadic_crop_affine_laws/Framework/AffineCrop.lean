/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.DensityTransport
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.Observation

namespace Submission.Obl.k4_dyadic_crop_affine_laws.Framework

open MeasureTheory Set

/-- An invertible diagonal change of real coefficient coordinates. -/
noncomputable def diagonalCoeffEquiv {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero ℝ ℝ (w i) (hw i)

lemma diagonalCoeffEquiv_apply {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0)
    (x : Fin n → ℝ) (i : Fin n) : diagonalCoeffEquiv w hw x i = w i * x i := rfl

lemma det_diagonalCoeffEquiv {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, w i ≠ 0) :
    LinearMap.det (diagonalCoeffEquiv w hw).toLinearMap = ∏ i, w i := by
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' (diagonalCoeffEquiv w hw).toLinearMap =
      Matrix.diagonal w := by
    ext i j
    simp [LinearMap.toMatrix'_apply, diagonalCoeffEquiv_apply, Matrix.diagonal_apply,
      Pi.single_apply, mul_ite]
  rw [hm, Matrix.det_diagonal]

noncomputable def cropCoefficientLinear (a : ℝ) (ha : a ≠ 0) :
    (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ) :=
  diagonalCoeffEquiv ![a, a, 1, a, a, 1] (by intro i; fin_cases i <;> simp [ha])

lemma cropCoefficientLinear_apply (a : ℝ) (ha : a ≠ 0) (x : Fin 6 → ℝ) :
    cropCoefficientLinear a ha x = ![a * x 0, a * x 1, x 2, a * x 3, a * x 4, x 5] := by
  ext i
  fin_cases i <;> simp [cropCoefficientLinear, diagonalCoeffEquiv_apply]

lemma det_cropCoefficientLinear (a : ℝ) (ha : a ≠ 0) :
    LinearMap.det (cropCoefficientLinear a ha).toLinearMap = a ^ 4 := by
  rw [cropCoefficientLinear, det_diagonalCoeffEquiv]
  simp [Fin.prod_univ_succ]
  ring

/-- The forward map from normalized coefficients to the original crop box. -/
noncomputable def cropCoefficientEquiv (a : ℝ) (ha : a ≠ 0)
    (c v : Fin 2 → ℝ) : (Fin 6 → ℝ) ≃ᵐ (Fin 6 → ℝ) :=
  affineObservationEquiv (cropCoefficientLinear a ha) ![c 0, c 1, 0, v 0, v 1, 0]

lemma cropCoefficientEquiv_apply (a : ℝ) (ha : a ≠ 0)
    (c v : Fin 2 → ℝ) (x : Fin 6 → ℝ) :
    cropCoefficientEquiv a ha c v x =
      ![c 0 + a * x 0, c 1 + a * x 1, x 2, v 0 + a * x 3, v 1 + a * x 4, x 5] := by
  rw [cropCoefficientEquiv, affineObservationEquiv_apply, cropCoefficientLinear_apply]
  ext i
  fin_cases i <;> simp <;> ring

lemma map_cropCoefficientEquiv_symm (a : ℝ) (ha : 0 < a) (c v : Fin 2 → ℝ) :
    (volume : Measure (Fin 6 → ℝ)).map (cropCoefficientEquiv a ha.ne' c v).symm =
      ENNReal.ofReal (a ^ 4) • volume := by
  rw [cropCoefficientEquiv, map_affineObservationEquiv_symm, det_cropCoefficientLinear,
    abs_of_nonneg (by positivity : 0 ≤ a ^ 4)]

/-- Natural trajectory indices are unchanged under the planar crop. -/
noncomputable def cropTrajectoryEquiv (a : ℝ) (ha : a ≠ 0)
    (c v : Fin 2 → ℝ) : Coefficients ≃ᵐ Coefficients :=
  (MeasurableEquiv.refl ℕ).prodCongr (cropCoefficientEquiv a ha c v)

lemma cropTrajectoryEquiv_apply (a : ℝ) (ha : a ≠ 0)
    (c v : Fin 2 → ℝ) (l : Coefficients) :
    cropTrajectoryEquiv a ha c v l =
      (l.1, ![c 0 + a * l.2 0, c 1 + a * l.2 1, l.2 2,
        v 0 + a * l.2 3, v 1 + a * l.2 4, l.2 5]) := by
  change (l.1, cropCoefficientEquiv a ha c v l.2) = _
  rw [cropCoefficientEquiv_apply]

lemma crop_hidden_coordinate (a : ℝ) (ha : a ≠ 0)
    (c v : Fin 2 → ℝ) (l : Coefficients) (t : ℝ) :
    trajectoryPoint (cropTrajectoryEquiv a ha c v l) t 3 = trajectoryPoint l t 3 := by
  simp [cropTrajectoryEquiv_apply, trajectoryPoint]

lemma crop_planar_coordinate (a : ℝ) (ha : a ≠ 0)
    (c v : Fin 2 → ℝ) (l : Coefficients) (t : ℝ) (j : Fin 2) :
    planarLine (cropTrajectoryEquiv a ha c v l) t j =
      c j + t * v j + a * planarLine l t j := by
  fin_cases j <;> simp [planarLine, cropTrajectoryEquiv_apply, trajectoryPoint] <;> ring

lemma crop_planar_velocity (a : ℝ) (ha : a ≠ 0)
    (c v : Fin 2 → ℝ) (l : Coefficients) (j : Fin 2) :
    planarVelocity (cropTrajectoryEquiv a ha c v l) j = v j + a * planarVelocity l j := by
  fin_cases j <;> simp [planarVelocity, cropTrajectoryEquiv_apply]

/-- The affine change of the three continuous observation coordinates. -/
noncomputable def cropBaseEquiv (a : ℝ) (ha : a ≠ 0) (c v : Fin 2 → ℝ) :
    EuclideanSpace ℝ (Fin 3) ≃ᵐ EuclideanSpace ℝ (Fin 3) :=
  chartBaseEquiv 0 1 (WithLp.toLp 2 c) (WithLp.toLp 2 v) !![a, 0; 0, a]
    (by norm_num) (by simp [Matrix.det_fin_two, ha])

lemma cropBaseEquiv_apply (a : ℝ) (ha : a ≠ 0) (c v : Fin 2 → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    cropBaseEquiv a ha c v x =
      WithLp.toLp 2 ![x 0, c 0 + x 0 * v 0 + a * x 1, c 1 + x 0 * v 1 + a * x 2] := by
  rw [cropBaseEquiv, chartBaseEquiv_apply]
  ext i
  fin_cases i <;> simp

lemma map_cropBaseEquiv_symm (a : ℝ) (ha : 0 < a) (c v : Fin 2 → ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).map (cropBaseEquiv a ha.ne' c v).symm =
      ENNReal.ofReal (a ^ 2) • volume := by
  rw [cropBaseEquiv, map_chartBaseEquiv_symm _ _ _ _ _ (by norm_num)]
  simp [Matrix.det_fin_two, pow_two, abs_of_nonneg (mul_self_nonneg a)]

/-- The pure observation retains its hidden bin under the planar crop. -/
lemma crop_pureObservation (a : ℝ) (ha : a ≠ 0) (c v : Fin 2 → ℝ)
    (B b : ℝ) (p : Coefficients × ℝ) :
    pureObservation B b (cropTrajectoryEquiv a ha c v p.1, p.2) =
      ((cropBaseEquiv a ha c v).prodCongr (MeasurableEquiv.refl ℤ))
        (pureObservation B b p) := by
  apply Prod.ext
  · change baseObservation (cropTrajectoryEquiv a ha c v p.1, p.2) =
      cropBaseEquiv a ha c v (baseObservation p)
    rw [cropBaseEquiv_apply]
    ext i
    fin_cases i <;>
      simp [baseObservation, trajectoryPoint, cropTrajectoryEquiv_apply] <;> ring
  · change ⌊B * trajectoryPoint (cropTrajectoryEquiv a ha c v p.1) p.2 3 / b⌋ =
      ⌊B * trajectoryPoint p.1 p.2 3 / b⌋
    rw [crop_hidden_coordinate]

/-- The three slope coordinates in their frozen Euclidean order. -/
def slopeVector (l : Coefficients) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5]

def cropSlopeMatrix (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, 0, 0; 0, a, 0; 0, 0, 1]

lemma det_cropSlopeMatrix (a : ℝ) : (cropSlopeMatrix a).det = a ^ 2 := by
  simp [cropSlopeMatrix, Matrix.det_fin_three, pow_two]

noncomputable def cropSlopeLinear (a : ℝ) (ha : a ≠ 0) :
    EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (cropSlopeMatrix a) (isUnit_iff_ne_zero.mpr (by rw [det_cropSlopeMatrix]; exact pow_ne_zero _ ha))

lemma det_cropSlopeLinear (a : ℝ) (ha : a ≠ 0) :
    LinearMap.det (cropSlopeLinear a ha).toLinearMap = a ^ 2 := by
  change LinearMap.det (Matrix.toLin (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (cropSlopeMatrix a)) = _
  rw [LinearMap.det_toLin, det_cropSlopeMatrix]

noncomputable def cropSlopeEquiv (a : ℝ) (ha : a ≠ 0) (v : Fin 2 → ℝ) :
    EuclideanSpace ℝ (Fin 3) ≃ᵐ EuclideanSpace ℝ (Fin 3) :=
  affineObservationEquiv (cropSlopeLinear a ha) (WithLp.toLp 2 ![v 0, v 1, 0])

lemma cropSlopeEquiv_apply (a : ℝ) (ha : a ≠ 0) (v : Fin 2 → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    cropSlopeEquiv a ha v x = WithLp.toLp 2 ![v 0 + a * x 0, v 1 + a * x 1, x 2] := by
  rw [cropSlopeEquiv, affineObservationEquiv_apply]
  change Matrix.toEuclideanLin (cropSlopeMatrix a) x + _ = _
  ext i
  fin_cases i <;>
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, cropSlopeMatrix,
      dotProduct, Fin.sum_univ_succ] <;> ring

lemma crop_slopeVector (a : ℝ) (ha : a ≠ 0) (c v : Fin 2 → ℝ) (l : Coefficients) :
    slopeVector (cropTrajectoryEquiv a ha c v l) = cropSlopeEquiv a ha v (slopeVector l) := by
  rw [cropSlopeEquiv_apply]
  ext i
  fin_cases i <;> simp [slopeVector, cropTrajectoryEquiv_apply]

lemma map_cropSlopeEquiv_symm (a : ℝ) (ha : 0 < a) (v : Fin 2 → ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).map (cropSlopeEquiv a ha.ne' v).symm =
      ENNReal.ofReal (a ^ 2) • volume := by
  rw [cropSlopeEquiv, map_affineObservationEquiv_symm, det_cropSlopeLinear,
    abs_of_nonneg (sq_nonneg a)]

end Submission.Obl.k4_dyadic_crop_affine_laws.Framework
