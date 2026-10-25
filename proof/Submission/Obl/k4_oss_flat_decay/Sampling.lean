import Submission.Obl.k4_oss_flat_decay.FourierDensity

namespace Submission.Obl.k4_oss_flat_decay

open MeasureTheory Set
open scoped MeasureTheory ENNReal NNReal

theorem lintegral_comp_mul_left_real (f : ℝ → ENNReal) (hf : Measurable f)
    {q : ℝ} (hq : q ≠ 0) :
    (∫⁻ x, f (q * x)) = ENNReal.ofReal |q⁻¹| * ∫⁻ v, f v := by
  rw [← lintegral_map hf (measurable_const_mul q), Real.map_volume_mul_left hq,
    lintegral_smul_measure, smul_eq_mul]

theorem lintegral_comp_mul_Icc (f : ℝ → ENNReal) (hf : Measurable f)
    {q : ℝ} (hq : q ≠ 0) (M : ℝ) :
    (∫⁻ x in Icc (-M) M, f (q * x)) =
      ENNReal.ofReal |q⁻¹| * ∫⁻ v in Icc (-(|q| * M)) (|q| * M), f v := by
  have hmem (x : ℝ) : q * x ∈ Icc (-(|q| * M)) (|q| * M) ↔ x ∈ Icc (-M) M := by
    simp only [mem_Icc, ← abs_le, abs_mul]
    exact mul_le_mul_iff_right₀ (abs_pos.mpr hq)
  rw [← lintegral_indicator measurableSet_Icc,
    ← lintegral_indicator measurableSet_Icc,
    ← lintegral_comp_mul_left_real _ (hf.indicator measurableSet_Icc) hq]
  apply lintegral_congr
  intro x
  simp only [indicator_apply, hmem]

/-- The averaged characteristic-function square is controlled by a collision
cap on the first law and a finite-scale cap on the sampling law. -/
theorem charFun_sampling_sq_le_collision
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : α (Icc (-1 : ℝ) 1)ᶜ = 0) (hβ : β (Icc (-2 : ℝ) 2)ᶜ = 0)
    {η r ρ q C s A : ℝ} (hη : 0 < η) (hηr : η ≤ r) (hr1 : r ≤ 1)
    (hρ : 0 < ρ) (hq : q ≠ 0) (hρq : ρ * (|q| * 3) ≤ 1 / 2)
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hcap : ∀ x : ℝ, β (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C * r ^ s))
    (hflat : collisionMass α (2 * ρ) ≤ ENNReal.ofReal A) :
    (∫ y, ‖charFun α (q * y)‖ ^ 2 ∂β) ≤
      (C * r ^ s / (2 * η) * |q⁻¹| * (4 * Real.pi / ρ) * A) + 2 * |q| * η := by
  have hr : 0 < r := hη.trans_le hηr
  let : IsProbabilityMeasure (uniformNoise η) := uniformNoise_probability hη
  have hF : Measurable (fun x : ℝ => ENNReal.ofReal (‖charFun α (q * x)‖ ^ 2)) := by fun_prop
  have hfreq : Measurable (fun v : ℝ => ENNReal.ofReal (‖charFun α v‖ ^ 2)) := by fun_prop
  have hbound : ENNReal.ofReal (∫ x, ‖charFun α (q * x)‖ ^ 2 ∂(β ∗ uniformNoise η)) ≤
      ENNReal.ofReal (C * r ^ s / (2 * η) * |q⁻¹| * (4 * Real.pi / ρ) * A) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (integrable_charFun_sq_comp α (β ∗ uniformNoise η) q) (ae_of_all _ fun x => sq_nonneg _)]
    calc
      _ ≤ ENNReal.ofReal (C * r ^ s / (2 * η)) *
          ∫⁻ x in Icc (-3 : ℝ) 3, ENNReal.ofReal (‖charFun α (q * x)‖ ^ 2) := by
        simpa only [show -(2 : ℝ) - 1 = -3 by norm_num,
          show (2 : ℝ) + 1 = 3 by norm_num] using
          lintegral_uniform_smoothing_le_on β hβ hη hηr hr1 hcap _ hF
      _ = ENNReal.ofReal (C * r ^ s / (2 * η)) * ENNReal.ofReal |q⁻¹| *
          ∫⁻ v in Icc (-(|q| * 3)) (|q| * 3), ENNReal.ofReal (‖charFun α v‖ ^ 2) := by
        rw [lintegral_comp_mul_Icc _ hfreq hq 3, mul_assoc]
      _ ≤ ENNReal.ofReal (C * r ^ s / (2 * η)) * ENNReal.ofReal |q⁻¹| *
          (ENNReal.ofReal (4 * Real.pi / ρ) * collisionMass α (2 * ρ)) :=
        mul_le_mul' le_rfl (lintegral_charFun_sq_Icc_le_collision α hρ hρq)
      _ ≤ ENNReal.ofReal (C * r ^ s / (2 * η)) * ENNReal.ofReal |q⁻¹| *
          (ENNReal.ofReal (4 * Real.pi / ρ) * ENNReal.ofReal A) := by gcongr
      _ = _ := by
        rw [← mul_assoc]
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C * r ^ s / (2 * η)),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * r ^ s / (2 * η) * |q⁻¹|),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * r ^ s / (2 * η) * |q⁻¹| * (4 * Real.pi / ρ))]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  exact (charFun_sq_integral_le_uniform_smoothing α β hα hη q).trans (by linarith)

end Submission.Obl.k4_oss_flat_decay
