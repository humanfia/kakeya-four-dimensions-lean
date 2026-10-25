import Submission.Obl.k4_scalar_crop_profile_transport.Types
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.DensityTransport
import Submission.Obl.k4_crop_base_finite_tail.BaseTransport

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set
open scoped ENNReal

/-- Forward matrix from cropped time-position coordinates to source coordinates. -/
def baseMatrix (a : ℝ) (z : Fin 2 → ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; a * (z 1 : ℝ), a]

lemma det_baseMatrix (a : ℝ) (z : Fin 2 → ℤ) : (baseMatrix a z).det = a := by
  simp [baseMatrix, Matrix.det_fin_two]

noncomputable def baseLinear (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 2)) (baseMatrix a z)
    (isUnit_iff_ne_zero.mpr (by simpa [det_baseMatrix] using ha))

lemma baseLinear_apply (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) (b : Fin 2 → ℝ) :
    baseLinear a ha z b = ![b 0, a * (z 1 : ℝ) * b 0 + a * b 1] := by
  ext i
  fin_cases i <;>
    simp [baseLinear, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin',
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, baseMatrix]

lemma det_baseLinear (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) :
    LinearMap.det (baseLinear a ha z).toLinearMap = a := by
  change LinearMap.det (Matrix.toLin (Pi.basisFun ℝ (Fin 2))
    (Pi.basisFun ℝ (Fin 2)) (baseMatrix a z)) = a
  rw [LinearMap.det_toLin, det_baseMatrix]

noncomputable def baseForward (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) :
    (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) :=
  k4_dyadic_crop_affine_laws.Framework.affineObservationEquiv
    (baseLinear a ha z) ![0, a * (z 0 : ℝ)]

lemma baseForward_apply (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) (b : Fin 2 → ℝ) :
    baseForward a ha z b = ![b 0, a * (z 0 : ℝ) + b 0 * (a * (z 1 : ℝ)) + a * b 1] := by
  rw [baseForward, k4_dyadic_crop_affine_laws.Framework.affineObservationEquiv_apply,
    baseLinear_apply]
  ext i
  fin_cases i <;> simp
  ring

lemma baseForward_symm_apply (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) (b : Fin 2 → ℝ) :
    (baseForward a ha z).symm b =
      ![b 0, (b 1 - a * (z 0 : ℝ) - b 0 * (a * (z 1 : ℝ))) / a] := by
  apply (baseForward a ha z).injective
  rw [MeasurableEquiv.apply_symm_apply, baseForward_apply]
  ext i
  fin_cases i <;> simp
  field_simp
  ring

noncomputable def obsEquiv (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) : Base ≃ᵐ Base :=
  (baseForward a ha z).symm.prodCongr (MeasurableEquiv.refl ℤ)

lemma obsEquiv_apply (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ) (b : Base) :
    obsEquiv a ha z b =
      (![b.1 0, (b.1 1 - a * (z 0 : ℝ) - b.1 0 * (a * (z 1 : ℝ))) / a], b.2) := by
  change ((baseForward a ha z).symm b.1, b.2) = _
  rw [baseForward_symm_apply]

lemma map_obs_reference (a : ℝ) (ha : 0 < a) (z : Fin 2 → ℤ) :
    BaseRef.map (obsEquiv a ha.ne' z) = ENNReal.ofReal a • BaseRef := by
  apply k4_dyadic_crop_affine_laws.Framework.map_prod_count_equiv
  change (volume : Measure (Fin 2 → ℝ)).map (baseForward a ha.ne' z).symm = _
  rw [baseForward, k4_dyadic_crop_affine_laws.Framework.map_affineObservationEquiv_symm,
    det_baseLinear, abs_of_pos ha]

lemma obs_crop (a : ℝ) (ha : a ≠ 0) (z : Fin 2 → ℤ)
    (N r : ℝ) (p : Inc) :
    Obs N r (CropInc a z p) = obsEquiv a ha z (Obs N r p) := by
  rw [obsEquiv_apply]
  apply Prod.ext
  · ext i
    fin_cases i
    · simp [Obs, CropInc]
    · simp [Obs, CropInc, Crop, y]
      field_simp
      ring
  · simp [Obs, CropInc, Crop, x]

/-- The supplied setwise lift is an exact pushforward identity. -/
lemma lift_map_eq (a p : ℝ) (hp : 0 < p) (z : Fin 2 → ℤ)
    (μ₀ μ : Measure Inc)
    (hlift : ∀ Z, MeasurableSet Z → ENNReal.ofReal p * μ Z =
      μ₀ {b | b.1 ∈ Cell a z ∧ CropInc a z b ∈ Z}) :
    μ = (ENNReal.ofReal p)⁻¹ • (μ₀.restrict (Cell a z ×ˢ univ)).map (CropInc a z) := by
  have heq : ENNReal.ofReal p • μ =
      (μ₀.restrict (Cell a z ×ˢ univ)).map (CropInc a z) := by
    ext Z hZ
    rw [Measure.smul_apply, smul_eq_mul, hlift Z hZ,
      Measure.map_apply (measurable_CropInc a z) hZ,
      Measure.restrict_apply ((measurable_CropInc a z) hZ)]
    congr 1
    ext b
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    exact and_comm
  rw [← heq, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    one_smul]

lemma map_obs_lift (a p : ℝ) (ha : a ≠ 0) (hp : 0 < p) (z : Fin 2 → ℤ)
    (N r : ℝ) (μ₀ μ : Measure Inc)
    (hlift : ∀ Z, MeasurableSet Z → ENNReal.ofReal p * μ Z =
      μ₀ {b | b.1 ∈ Cell a z ∧ CropInc a z b ∈ Z}) :
    μ.map (Obs N r) = (ENNReal.ofReal p)⁻¹ •
      ((μ₀.restrict (Cell a z ×ˢ univ)).map (Obs N r)).map (obsEquiv a ha z) := by
  rw [lift_map_eq a p hp z μ₀ μ hlift,
    Measure.map_smul _ (measurable_Obs N r).aemeasurable,
    Measure.map_map (measurable_Obs N r) (measurable_CropInc a z),
    show Obs N r ∘ CropInc a z = obsEquiv a ha z ∘ Obs N r
      from funext (obs_crop a ha z N r),
    ← Measure.map_map (obsEquiv a ha z).measurable (measurable_Obs N r)]

/-- A cropped pure density gives a density for the unnormalized source restriction. -/
lemma raw_density_law (a p : ℝ) (ha : 0 < a) (hp : 0 < p) (z : Fin 2 → ℤ)
    (N r : ℝ) (μ₀ μ : Measure Inc) (g : Base → ENNReal) (hg : Measurable g)
    (hlift : ∀ Z, MeasurableSet Z → ENNReal.ofReal p * μ Z =
      μ₀ {b | b.1 ∈ Cell a z ∧ CropInc a z b ∈ Z})
    (hlaw : μ.map (Obs N r) = BaseRef.withDensity g) :
    (μ₀.restrict (Cell a z ×ˢ univ)).map (Obs N r) =
      BaseRef.withDensity (fun b => (ENNReal.ofReal p / ENNReal.ofReal a) *
        g (obsEquiv a ha.ne' z b)) := by
  apply k4_crop_base_finite_tail.BaseTransport.pullback_density_law
    (obsEquiv a ha.ne' z) BaseRef BaseRef (ENNReal.ofReal a) (ENNReal.ofReal p)
    (ENNReal.ofReal_ne_zero_iff.mpr ha) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    (map_obs_reference a ha z)
    ((μ₀.restrict (Cell a z ×ˢ univ)).map (Obs N r)) g hg
  rw [← map_obs_lift a p ha.ne' hp z N r μ₀ μ hlift]
  exact hlaw

end Submission.Obl.k4_scalar_crop_profile_transport
