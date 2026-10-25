import Submission.Obl.k4_scalar_normalized_exact_refinement.Coordinates
import Submission.Obl.k4_dk4_smoothed_problem.CoefficientCoordinates
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.DensityTransport

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private abbrev pack := k4_dk4_smoothed_problem.Framework.concatenateCoefficients 2 3

private lemma pack_apply (p : (Fin 2 → ℝ) × (Fin 3 → ℝ)) :
    pack p = ![p.1 0, p.1 1, p.2 0, p.2 1, p.2 2] := by
  funext i
  fin_cases i <;> rfl

def prediction (P : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  MvPolynomial.eval ![t, a 0 + t * a 1] P

def predictionCoefficients (P : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![prediction P a 0,
    4 * prediction P a (1 / 2) - prediction P a 1 - 3 * prediction P a 0,
    2 * (prediction P a 1 - 2 * prediction P a (1 / 2) + prediction P a 0)]

lemma continuous_predictionCoefficients (P : MvPolynomial (Fin 2) ℝ) :
    Continuous (predictionCoefficients P) := by
  have hp (t : ℝ) : Continuous (fun a : Fin 2 → ℝ => prediction P a t) := by
    apply (MvPolynomial.continuous_eval P).comp
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [predictionCoefficients] <;> fun_prop

def shearBlockEquiv (P : MvPolynomial (Fin 2) ℝ) :
    ((Fin 2 → ℝ) × (Fin 3 → ℝ)) ≃ᵐ ((Fin 2 → ℝ) × (Fin 3 → ℝ)) where
  toFun p := (p.1, p.2 - predictionCoefficients P p.1)
  invFun p := (p.1, p.2 + predictionCoefficients P p.1)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := measurable_fst.prodMk
    (measurable_snd.sub ((continuous_predictionCoefficients P).measurable.comp measurable_fst))
  measurable_invFun := measurable_fst.prodMk
    (measurable_snd.add ((continuous_predictionCoefficients P).measurable.comp measurable_fst))

lemma measurePreserving_shearBlockEquiv (P : MvPolynomial (Fin 2) ℝ) :
    MeasurePreserving (shearBlockEquiv P) (volume.prod volume) (volume.prod volume) := by
  apply (MeasurePreserving.id (volume : Measure (Fin 2 → ℝ))).skew_product
    (g := fun a b => b - predictionCoefficients P a)
    (μc := (volume : Measure (Fin 3 → ℝ)))
    (μd := (volume : Measure (Fin 3 → ℝ)))
  · exact (shearBlockEquiv P).measurable.snd
  · apply Filter.Eventually.of_forall
    intro a
    simpa only [sub_eq_add_neg] using
      map_add_right_eq_self (volume : Measure (Fin 3 → ℝ)) (-predictionCoefficients P a)

def shearCoefficientEquiv (P : MvPolynomial (Fin 2) ℝ) : (Fin 5 → ℝ) ≃ᵐ (Fin 5 → ℝ) :=
  pack.symm.trans ((shearBlockEquiv P).trans pack)

lemma measurePreserving_shearCoefficientEquiv (P : MvPolynomial (Fin 2) ℝ) :
    MeasurePreserving (shearCoefficientEquiv P) volume volume := by
  have hp := k4_dk4_smoothed_problem.Framework.measurePreserving_concatenateCoefficients 2 3
  exact hp.comp ((measurePreserving_shearBlockEquiv P).comp (hp.symm pack))

lemma shearCoefficientEquiv_apply (P : MvPolynomial (Fin 2) ℝ) (a : Fin 5 → ℝ) :
    shearCoefficientEquiv P a = (normalizeLine P 0 1 0 0 1 1 (0, a)).2 := by
  obtain ⟨p, rfl⟩ := pack.surjective a
  change pack ((shearBlockEquiv P) (pack.symm (pack p))) = _
  rw [pack.symm_apply_apply]
  change pack (p.1, p.2 - predictionCoefficients P p.1) = _
  rw [pack_apply, pack_apply]
  funext i
  fin_cases i <;>
    simp [normalizeLine, y, x, k4_scalar_linear_critical_extremizers.Split.y,
      k4_scalar_linear_critical_extremizers.Split.x,
      predictionCoefficients, prediction] <;> ring

/-- The linear part of the affine coefficient normalization. -/
def coefficientMatrix (t₀ dt J δ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1 / J, t₀ / J, 0, 0, 0;
    0, dt / J, 0, 0, 0;
    0, 0, 1 / δ, t₀ / δ, t₀ ^ 2 / δ;
    0, 0, 0, dt / δ, 2 * t₀ * dt / δ;
    0, 0, 0, 0, dt ^ 2 / δ]

lemma det_coefficientMatrix (t₀ dt J δ : ℝ) :
    (coefficientMatrix t₀ dt J δ).det = dt ^ 4 / (J ^ 2 * δ ^ 3) := by
  have htri : (coefficientMatrix t₀ dt J δ).IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [coefficientMatrix] at *
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [coefficientMatrix, Fin.prod_univ_succ, div_eq_mul_inv]
  ring

def coefficientLinearEquiv (t₀ dt J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) : (Fin 5 → ℝ) ≃ₗ[ℝ] (Fin 5 → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 5)) (coefficientMatrix t₀ dt J δ)
    (isUnit_iff_ne_zero.mpr (by rw [det_coefficientMatrix]; positivity))

def affineCoefficientEquiv (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) : (Fin 5 → ℝ) ≃ᵐ (Fin 5 → ℝ) :=
  k4_dyadic_crop_affine_laws.Framework.affineObservationEquiv
    (coefficientLinearEquiv t₀ dt J δ hdt hJ hδ)
    ![-(u + t₀ * v) / J, -dt * v / J, 0, 0, 0]

lemma affineCoefficientEquiv_apply (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) (a : Fin 5 → ℝ) :
    affineCoefficientEquiv t₀ dt u v J δ hdt hJ hδ a =
      (normalizeLine 0 t₀ dt u v J δ (0, a)).2 := by
  rw [affineCoefficientEquiv,
    k4_dyadic_crop_affine_laws.Framework.affineObservationEquiv_apply]
  funext i
  fin_cases i <;>
    simp [coefficientLinearEquiv, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin',
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ, coefficientMatrix,
      normalizeLine, y, x, k4_scalar_linear_critical_extremizers.Split.y,
      k4_scalar_linear_critical_extremizers.Split.x] <;> ring

lemma map_affineCoefficientEquiv (t₀ dt u v J δ : ℝ)
    (hdt : 0 < dt) (hJ : 0 < J) (hδ : 0 < δ) :
    (volume : Measure (Fin 5 → ℝ)).map
      (affineCoefficientEquiv t₀ dt u v J δ hdt.ne' hJ.ne' hδ.ne') =
      ENNReal.ofReal (J ^ 2 * δ ^ 3 / dt ^ 4) • volume := by
  let L := coefficientLinearEquiv t₀ dt J δ hdt.ne' hJ.ne' hδ.ne'
  let b : Fin 5 → ℝ := ![-(u + t₀ * v) / J, -dt * v / J, 0, 0, 0]
  have hd : LinearMap.det (coefficientLinearEquiv t₀ dt J δ hdt.ne' hJ.ne' hδ.ne').toLinearMap =
      dt ^ 4 / (J ^ 2 * δ ^ 3) := by
    change LinearMap.det (Matrix.toLin (Pi.basisFun ℝ (Fin 5))
      (Pi.basisFun ℝ (Fin 5)) (coefficientMatrix t₀ dt J δ)) = _
    rw [LinearMap.det_toLin, det_coefficientMatrix]
  change (volume : Measure (Fin 5 → ℝ)).map ((fun z => z + b) ∘ (L : _ → _)) = _
  have hL : Measurable (L : (Fin 5 → ℝ) → (Fin 5 → ℝ)) :=
    L.toContinuousLinearEquiv.continuous.measurable
  rw [← Measure.map_map (by fun_prop) hL]
  change ((volume : Measure (Fin 5 → ℝ)).map (L.toLinearMap : _ → _)).map (fun z => z + b) = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.isUnit_det'.ne_zero,
    Measure.map_smul _ (by fun_prop), map_add_right_eq_self]
  change ENNReal.ofReal |(LinearMap.det L.toLinearMap)⁻¹| • volume = _
  rw [show LinearMap.det L.toLinearMap = dt ^ 4 / (J ^ 2 * δ ^ 3) from hd,
    inv_div, abs_of_pos (by positivity)]

def normalizationCoefficientEquiv (P : MvPolynomial (Fin 2) ℝ)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) :
    (Fin 5 → ℝ) ≃ᵐ (Fin 5 → ℝ) :=
  (shearCoefficientEquiv P).trans (affineCoefficientEquiv t₀ dt u v J δ hdt hJ hδ)

lemma normalizationCoefficientEquiv_apply (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) (a : Fin 5 → ℝ) :
    normalizationCoefficientEquiv P t₀ dt u v J δ hdt hJ hδ a =
      (normalizeLine P t₀ dt u v J δ (0, a)).2 := by
  change affineCoefficientEquiv t₀ dt u v J δ hdt hJ hδ (shearCoefficientEquiv P a) = _
  rw [affineCoefficientEquiv_apply, shearCoefficientEquiv_apply]
  exact congrArg Prod.snd (normalizeEquiv_apply P hP t₀ dt u v J δ hdt hJ hδ (0, a))

lemma normalizationCoefficientEquiv_symm_apply (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ dt u v J δ : ℝ)
    (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) (a : Fin 5 → ℝ) :
    (normalizationCoefficientEquiv P t₀ dt u v J δ hdt hJ hδ).symm a =
      (normalizeLine (-P) 0 1 0 0 1 1
        (normalizeLine 0 (-t₀ / dt) dt⁻¹ (-(u + t₀ * v) / J) (-dt * v / J) J⁻¹ δ⁻¹ (0, a))).2 := by
  apply (normalizationCoefficientEquiv P t₀ dt u v J δ hdt hJ hδ).injective
  rw [MeasurableEquiv.apply_symm_apply,
    normalizationCoefficientEquiv_apply P hP t₀ dt u v J δ hdt hJ hδ]
  have h := congrArg Prod.snd
    ((normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).apply_symm_apply (0, a))
  rw [normalizeEquiv_apply] at h
  exact h.symm

lemma normalizeEquiv_eq_prod (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) :
    normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ =
      (MeasurableEquiv.refl ℕ).prodCongr
        (normalizationCoefficientEquiv P t₀ dt u v J δ hdt hJ hδ) := by
  apply MeasurableEquiv.ext
  funext l
  rw [normalizeEquiv_apply]
  apply Prod.ext
  · rfl
  · change (normalizeLine P t₀ dt u v J δ l).2 =
      normalizationCoefficientEquiv P t₀ dt u v J δ hdt hJ hδ l.2
    rw [normalizationCoefficientEquiv_apply P hP]
    rfl

lemma map_normalizationCoefficientEquiv (P : MvPolynomial (Fin 2) ℝ)
    (t₀ dt u v J δ : ℝ) (hdt : 0 < dt) (hJ : 0 < J) (hδ : 0 < δ) :
    (volume : Measure (Fin 5 → ℝ)).map
      (normalizationCoefficientEquiv P t₀ dt u v J δ hdt.ne' hJ.ne' hδ.ne') =
      ENNReal.ofReal (J ^ 2 * δ ^ 3 / dt ^ 4) • volume := by
  change (volume : Measure (Fin 5 → ℝ)).map
    (affineCoefficientEquiv t₀ dt u v J δ hdt.ne' hJ.ne' hδ.ne' ∘ shearCoefficientEquiv P) = _
  rw [← Measure.map_map (affineCoefficientEquiv _ _ _ _ _ _ _ _ _).measurable
    (shearCoefficientEquiv P).measurable,
    (measurePreserving_shearCoefficientEquiv P).map_eq,
    map_affineCoefficientEquiv t₀ dt u v J δ hdt hJ hδ]

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
