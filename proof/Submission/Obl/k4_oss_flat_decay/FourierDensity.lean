import Submission.Obl.k4_oss_flat_decay.Collision
import Submission.Obl.k4_oss_flat_decay.Characteristic
import Submission.Obl.k4_oss_flat_decay.Plancherel

namespace Submission.Obl.k4_oss_flat_decay

open MeasureTheory Set
open scoped MeasureTheory ENNReal NNReal FourierTransform

/-- The characteristic function of the smoothed law is the ordinary Fourier
transform of its density, with the physical frequency normalization. -/
theorem charFun_uniform_smoothing_eq_fourier (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
    charFun (μ ∗ uniformNoise δ) v =
      𝓕 (smoothedFunction μ δ) (-(2 * Real.pi)⁻¹ * v) := by
  rw [uniform_smoothing_eq_withDensity μ hδ, charFun_apply_real,
    integral_withDensity_eq_integral_toReal_smul (measurable_smoothingDensity μ δ)
      (ae_of_all _ fun x => lt_top_iff_ne_top.mpr (smoothingDensity_ne_top μ hδ x)),
    Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  have hphase : -2 * Real.pi * inner ℝ x (-(2 * Real.pi)⁻¹ * v) = v * x := by
    simp only [RCLike.inner_apply, conj_trivial]
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  simp only [smoothedFunction, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- Physical normalization of Plancherel for a uniformly smoothed law. -/
theorem integral_charFun_uniform_smoothing_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ v, ‖charFun (μ ∗ uniformNoise δ) v‖ ^ 2) =
      2 * Real.pi * ∫ x, ‖smoothedFunction μ δ x‖ ^ 2 := by
  simp_rw [charFun_uniform_smoothing_eq_fourier μ hδ]
  rw [Measure.integral_comp_mul_left
      (fun w : ℝ => ‖𝓕 (smoothedFunction μ δ) w‖ ^ 2) (-(2 * Real.pi)⁻¹),
    integral_norm_sq_fourier (integrable_smoothedFunction μ hδ) (memLp_smoothedFunction μ hδ)]
  have hscale : |(-(2 * Real.pi)⁻¹ : ℝ)⁻¹| = 2 * Real.pi := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [hscale, smul_eq_mul]

theorem integrable_charFun_uniform_smoothing_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun v => ‖charFun (μ ∗ uniformNoise δ) v‖ ^ 2) := by
  have hm := memLp_fourier (integrable_smoothedFunction μ hδ) (memLp_smoothedFunction μ hδ)
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hscale : (-(2 * Real.pi)⁻¹ : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  simpa only [charFun_uniform_smoothing_eq_fourier μ hδ] using hi.comp_mul_left' hscale

/-- A direct upper bound on the full frequency square integral of the smoothed
law, in terms of the original law's collision probability. -/
theorem lintegral_charFun_uniform_smoothing_sq_le_collision
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ v, ENNReal.ofReal (‖charFun (μ ∗ uniformNoise δ) v‖ ^ 2)) ≤
      ENNReal.ofReal (Real.pi / δ) * collisionMass μ (2 * δ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_charFun_uniform_smoothing_sq μ hδ)
    (ae_of_all _ fun v => sq_nonneg _), integral_charFun_uniform_smoothing_sq μ hδ,
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
  calc _ ≤ ENNReal.ofReal (2 * Real.pi) *
        ((ENNReal.ofReal (2 * δ))⁻¹ * collisionMass μ (2 * δ)) :=
      mul_le_mul' le_rfl (ofReal_integral_smoothedFunction_sq_le_collision μ hδ)
    _ = _ := by
      rw [← mul_assoc, mul_comm (ENNReal.ofReal (2 * Real.pi)),
        ← ENNReal.div_eq_inv_mul,
        ← ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * δ)]
      congr 2
      field_simp

theorem charFun_sq_le_four_mul_smoothed (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {r R v : ℝ} (hr : 0 < r) (hRr : r * R ≤ 1 / 2) (hv : |v| ≤ R) :
    ‖charFun μ v‖ ^ 2 ≤ 4 * ‖charFun (μ ∗ uniformNoise r) v‖ ^ 2 := by
  let : IsProbabilityMeasure (uniformNoise r) := uniformNoise_probability hr
  have hn := one_half_le_norm_charFun_uniformNoise hr hRr hv
  have hcoef : 0 ≤ 4 * ‖charFun (uniformNoise r) v‖ ^ 2 - 1 := by
    nlinarith [sq_nonneg (‖charFun (uniformNoise r) v‖ - 1 / 2)]
  have hm := mul_nonneg (sq_nonneg ‖charFun μ v‖) hcoef
  rw [charFun_conv, norm_mul, mul_pow]
  nlinarith

/-- At frequencies below the reciprocal smoothing radius, the original
characteristic function's square integral is controlled by collisions. -/
theorem lintegral_charFun_sq_Icc_le_collision (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {r R : ℝ} (hr : 0 < r) (hRr : r * R ≤ 1 / 2) :
    (∫⁻ v in Icc (-R) R, ENNReal.ofReal (‖charFun μ v‖ ^ 2)) ≤
      ENNReal.ofReal (4 * Real.pi / r) * collisionMass μ (2 * r) := by
  calc
    _ ≤ ∫⁻ v in Icc (-R) R, ENNReal.ofReal
        (4 * ‖charFun (μ ∗ uniformNoise r) v‖ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      exact ENNReal.ofReal_le_ofReal (charFun_sq_le_four_mul_smoothed μ hr hRr (abs_le.mpr hv))
    _ = ENNReal.ofReal 4 *
        ∫⁻ v in Icc (-R) R, ENNReal.ofReal (‖charFun (μ ∗ uniformNoise r) v‖ ^ 2) := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal 4 *
        ∫⁻ v, ENNReal.ofReal (‖charFun (μ ∗ uniformNoise r) v‖ ^ 2) :=
      mul_le_mul' le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal (Real.pi / r) * collisionMass μ (2 * r)) :=
      mul_le_mul' le_rfl (lintegral_charFun_uniform_smoothing_sq_le_collision μ hr)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      congr 2
      ring

end Submission.Obl.k4_oss_flat_decay
