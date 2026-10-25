import Submission.Obl.k4_dyadic_crop_worlds.Geometry

namespace Submission.Obl.k4_dyadic_crop_worlds

open MeasureTheory Set
noncomputable section

def cropScale (a : ℝ) : Coeff := ![a⁻¹, a⁻¹, 1, a⁻¹, a⁻¹, 1]
def cropShift (q : Label) : Coeff := ![-(q 0 : ℝ), -(q 1 : ℝ), 0, -(q 2 : ℝ), -(q 3 : ℝ), 0]
def cropLinear (a : ℝ) : Coeff →ₗ[ℝ] Coeff := Matrix.toLin' (Matrix.diagonal (cropScale a))

lemma cropLinear_apply (a : ℝ) (x : Coeff) (i : Fin 6) :
    cropLinear a x i = cropScale a i * x i := by
  simp [cropLinear, Matrix.diagonal_toLin']

lemma cropCoeff_eq (a : ℝ) (q : Label) :
    cropCoeff a q = (fun x : Coeff => x + cropShift q) ∘ cropLinear a := by
  ext x i
  change cropCoeff a q x i = cropLinear a x i + cropShift q i
  rw [cropLinear_apply]
  fin_cases i <;> simp [cropCoeff, cropScale, cropShift, div_eq_mul_inv, mul_comm, sub_eq_add_neg]

lemma cropLinear_det (a : ℝ) :
    (Matrix.diagonal (cropScale a)).det = (a⁻¹) ^ 4 := by
  simp [Matrix.det_diagonal, cropScale, Fin.prod_univ_succ]
  ring

lemma map_cropCoeff_volume {a : ℝ} (ha : a ≠ 0) (q : Label) :
    Measure.map (cropCoeff a q) volume = ENNReal.ofReal (a ^ 4) • (volume : Measure Coeff) := by
  have hdet : (Matrix.diagonal (cropScale a)).det ≠ 0 := by
    rw [cropLinear_det]
    exact pow_ne_zero _ (inv_ne_zero ha)
  have hm : Measure.map (cropLinear a) volume = ENNReal.ofReal (a ^ 4) • (volume : Measure Coeff) := by
    rw [cropLinear, Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, cropLinear_det]
    simp only [inv_pow, inv_inv, abs_of_nonneg (by positivity : 0 ≤ a ^ 4)]
  rw [cropCoeff_eq, ← Measure.map_map (by fun_prop) (LinearMap.continuous_on_pi _).measurable,
    hm, Measure.map_smul _ (by fun_prop), map_add_right_eq_self]

lemma map_cropCoeff_restrict {a : ℝ} (ha : a ≠ 0) (q : Label) (A : Set Coeff) :
    Measure.map (cropCoeff a q) (volume.restrict A) =
      ENNReal.ofReal (a ^ 4) • volume.restrict (cropCoeff a q '' A) := by
  have h := (coeffHomeomorph ha q).measurableEmbedding.restrict_map
    (volume : Measure Coeff) (cropCoeff a q '' A)
  change (Measure.map (cropCoeff a q) volume).restrict (cropCoeff a q '' A) =
    Measure.map (cropCoeff a q) (volume.restrict (cropCoeff a q ⁻¹' (cropCoeff a q '' A))) at h
  rw [preimage_image_eq A (show Function.Injective (cropCoeff a q) from (coeffHomeomorph ha q).injective)] at h
  rw [← h, map_cropCoeff_volume ha q, Measure.restrict_smul]

lemma cropPrior_probability (ν : Measure Line) [IsProbabilityMeasure ν]
    (a : ℝ) (q : Label) {p : ℝ} (hp : 0 < p) (heq : p = (ν (cell a q)).toReal) :
    IsProbabilityMeasure (cropPrior ν a q p) := by
  apply isProbabilityMeasure_iff.mpr
  rw [cropPrior, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_cropLine a q).measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, heq,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.inv_mul_cancel (by rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← heq]; positivity)
    (measure_ne_top _ _)

lemma cropPrior_incidence_mass (ν : Measure Line) [IsProbabilityMeasure ν]
    {a : ℝ} (ha : a ≠ 0) (q : Label) (p : ℝ) {E : Set Incident} (hE : MeasurableSet E) :
    (((cropPrior ν a q p).prod volume).restrict (cropEvent E a q)) univ =
      (ENNReal.ofReal p)⁻¹ * (ν.prod volume) (E ∩ (cell a q ×ˢ univ)) := by
  rw [Measure.restrict_apply_univ, cropPrior, Measure.prod_smul_left, Measure.smul_apply,
    smul_eq_mul]
  have hm : (Measure.map (cropLine a q) (ν.restrict (cell a q))).prod volume =
      Measure.map (cropPoint a q) ((ν.restrict (cell a q)).prod volume) := by
    have h := Measure.map_prod_map (ν.restrict (cell a q)) (volume : Measure ℝ)
      (continuous_cropLine a q).measurable (measurable_id : Measurable (id : ℝ → ℝ))
    rw [Measure.map_id] at h
    exact h
  rw [hm, Measure.map_apply (continuous_cropPoint a q).measurable (measurable_cropEvent ha q hE)]
  rw [cropEvent, preimage_image_eq _ (cropPoint_injective ha q)]
  rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply
    (hE.inter ((measurable_cell a q).prod MeasurableSet.univ))]
  congr 1
  congr 1
  ext z
  simp only [mem_inter_iff]
  tauto

end
end Submission.Obl.k4_dyadic_crop_worlds
