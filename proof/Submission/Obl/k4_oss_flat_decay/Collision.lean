import Submission.Obl.k4_oss_flat_decay.Regularization

namespace Submission.Obl.k4_oss_flat_decay

open MeasureTheory Set
open scoped MeasureTheory ENNReal NNReal

noncomputable def collisionMass (μ : Measure ℝ) (r : ℝ) : ENNReal :=
  (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ r}

private theorem interval_section (x r : ℝ) :
    Prod.mk x ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ r} = Icc (x - r) (x + r) := by
  ext y
  simp only [mem_preimage, mem_ofPred_eq, mem_Icc]
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem measurable_interval_mass (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    Measurable (fun x : ℝ => μ (Icc (x - r) (x + r))) := by
  have h := measurable_measure_prodMk_left (ν := μ)
    (measurableSet_le (measurable_fst.sub measurable_snd).abs measurable_const
      : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| ≤ r})
  simpa only [interval_section] using h

theorem collisionMass_eq_lintegral (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    collisionMass μ r = ∫⁻ x, μ (Icc (x - r) (x + r)) ∂μ := by
  have hs : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| ≤ r} :=
    measurableSet_le (measurable_fst.sub measurable_snd).abs measurable_const
  rw [collisionMass, Measure.prod_apply hs]
  simp only [interval_section]

theorem collisionMass_mono (μ : Measure ℝ) {r u : ℝ} (hru : r ≤ u) :
    collisionMass μ r ≤ collisionMass μ u :=
  measure_mono (fun _ hp => hp.trans hru)

noncomputable def smoothingDensity (μ : Measure ℝ) (δ x : ℝ) : ENNReal :=
  (ENNReal.ofReal (2 * δ))⁻¹ * μ (Icc (x - δ) (x + δ))

theorem measurable_smoothingDensity (μ : Measure ℝ) [SFinite μ] (δ : ℝ) :
    Measurable (smoothingDensity μ δ) :=
  measurable_const.mul (measurable_interval_mass μ δ)

theorem smoothingDensity_ne_top (μ : Measure ℝ) [IsFiniteMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : smoothingDensity μ δ x ≠ ∞ := by
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))))
    (measure_ne_top μ _)

/-- The smoothed law is given by its explicit sliding-interval density. -/
theorem uniform_smoothing_eq_withDensity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) :
    μ ∗ uniformNoise δ = volume.withDensity (smoothingDensity μ δ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_uniform_smoothing μ hδ f hf,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_smoothingDensity μ δ) hf]
  have hc : (ENNReal.ofReal (2 * δ))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  rw [← lintegral_const_mul' _ _ hc]
  apply lintegral_congr
  intro x
  dsimp [smoothingDensity]
  ring

/-- The square integral of the smoothing density is bounded directly by a
collision probability at twice the smoothing radius. -/
theorem lintegral_smoothingDensity_sq_le_collision (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ x, (smoothingDensity μ δ x) ^ 2) ≤
      (ENNReal.ofReal (2 * δ))⁻¹ * collisionMass μ (2 * δ) := by
  let : IsProbabilityMeasure (uniformNoise δ) := uniformNoise_probability hδ
  have hc : (ENNReal.ofReal (2 * δ))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  have hdens : Measurable (smoothingDensity μ δ) := measurable_smoothingDensity μ δ
  have heq : (∫⁻ x, (smoothingDensity μ δ x) ^ 2) =
      ∫⁻ x, smoothingDensity μ δ x ∂(μ ∗ uniformNoise δ) := by
    rw [lintegral_uniform_smoothing μ hδ _ hdens]
    rw [← lintegral_const_mul' _ _ hc]
    apply lintegral_congr
    intro x
    dsimp [smoothingDensity]
    ring
  rw [heq, Measure.lintegral_conv hdens, collisionMass_eq_lintegral,
    ← lintegral_const_mul' _ _ hc]
  apply lintegral_mono
  intro x
  calc
    _ ≤ ∫⁻ _z, (ENNReal.ofReal (2 * δ))⁻¹ *
        μ (Icc (x - 2 * δ) (x + 2 * δ)) ∂(uniformNoise δ) := by
      apply lintegral_mono_ae
      filter_upwards [mem_ae_iff.mpr (uniformNoise_support δ)] with z hz
      apply mul_le_mul' le_rfl
      exact measure_mono (Icc_subset_Icc (by linarith [hz.1]) (by linarith [hz.2]))
    _ = _ := by simp

theorem lintegral_smoothingDensity_eq_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) : (∫⁻ x, smoothingDensity μ δ x) = 1 := by
  let : IsProbabilityMeasure (uniformNoise δ) := uniformNoise_probability hδ
  calc
    (∫⁻ x, smoothingDensity μ δ x) =
        (volume.withDensity (smoothingDensity μ δ)) univ := by
      rw [withDensity_apply _ MeasurableSet.univ]
      simp
    _ = (μ ∗ uniformNoise δ) univ := by rw [← uniform_smoothing_eq_withDensity μ hδ]
    _ = 1 := measure_univ

theorem integrable_smoothingDensity_toReal (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) : Integrable (fun x => (smoothingDensity μ δ x).toReal) :=
  integrable_toReal_of_lintegral_ne_top (measurable_smoothingDensity μ δ).aemeasurable
    (by rw [lintegral_smoothingDensity_eq_one μ hδ]; exact ENNReal.one_ne_top)

noncomputable def smoothedFunction (μ : Measure ℝ) (δ x : ℝ) : ℂ :=
  (smoothingDensity μ δ x).toReal

theorem measurable_smoothedFunction (μ : Measure ℝ) [SFinite μ] (δ : ℝ) :
    Measurable (smoothedFunction μ δ) :=
  Complex.continuous_ofReal.measurable.comp
    (measurable_smoothingDensity μ δ).ennreal_toReal

theorem integrable_smoothedFunction (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) : Integrable (smoothedFunction μ δ) := by
  apply (integrable_norm_iff (measurable_smoothedFunction μ δ).aestronglyMeasurable).mp
  simpa only [smoothedFunction, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg] using integrable_smoothingDensity_toReal μ hδ

theorem memLp_smoothedFunction (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) : MemLp (smoothedFunction μ δ) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_smoothedFunction μ δ).aestronglyMeasurable).mpr
  have hfinite : (∫⁻ x, (smoothingDensity μ δ x) ^ 2) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (lintegral_smoothingDensity_sq_le_collision μ hδ)
    exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))))
      (measure_ne_top (μ.prod μ) _)
  have hsq := integrable_toReal_of_lintegral_ne_top
    ((measurable_smoothingDensity μ δ).pow_const 2).aemeasurable hfinite
  simpa only [smoothedFunction, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_pow] using hsq

theorem ofReal_integral_smoothedFunction_sq_le_collision
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (∫ x, ‖smoothedFunction μ δ x‖ ^ 2) ≤
      (ENNReal.ofReal (2 * δ))⁻¹ * collisionMass μ (2 * δ) := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (measurable_smoothedFunction μ δ).aestronglyMeasurable).mp (memLp_smoothedFunction μ hδ)
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => sq_nonneg _)]
  have heq (x : ℝ) : ENNReal.ofReal (‖smoothedFunction μ δ x‖ ^ 2) =
      (smoothingDensity μ δ x) ^ 2 := by
    simp only [smoothedFunction, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (smoothingDensity_ne_top μ hδ x)]
  simp_rw [heq]
  exact lintegral_smoothingDensity_sq_le_collision μ hδ

end Submission.Obl.k4_oss_flat_decay
