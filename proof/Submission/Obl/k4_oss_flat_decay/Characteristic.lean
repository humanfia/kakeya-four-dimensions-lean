import Submission.Obl.k4_oss_flat_decay.Smoothing

namespace Submission.Obl.k4_oss_flat_decay

open MeasureTheory Set
open scoped MeasureTheory ENNReal NNReal

/-- Real exponential phases are Lipschitz with constant one. -/
theorem norm_exp_phase_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have hfactor : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp ((b : ℂ) * Complex.I) *
        (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

theorem norm_charFun_sub_le_of_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ} (hsupp : μ (Icc (-M) M)ᶜ = 0) (a b : ℝ) :
    ‖charFun μ a - charFun μ b‖ ≤ M * |a - b| := by
  have hexp (v : ℝ) : Integrable (fun x : ℝ =>
      Complex.exp (((v * x : ℝ) : ℂ) * Complex.I)) μ :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
      simp only [Complex.norm_exp_ofReal_mul_I, le_refl])
  rw [charFun_apply_real, charFun_apply_real]
  simp_rw [← Complex.ofReal_mul]
  rw [← integral_sub (hexp a) (hexp b)]
  calc _ ≤ ∫ x, ‖Complex.exp (((a * x : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((b * x : ℝ) : ℂ) * Complex.I)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, M * |a - b| ∂μ := by
      apply integral_mono_ae ((hexp a).sub (hexp b)).norm (integrable_const _)
      filter_upwards [mem_ae_iff.mpr hsupp] with x hx
      calc _ ≤ |a * x - b * x| := norm_exp_phase_sub_le _ _
        _ = |a - b| * |x| := by rw [← sub_mul, abs_mul]
        _ ≤ M * |a - b| := by
          have hnorm : |x| ≤ M := abs_le.mpr hx
          nlinarith [mul_le_mul_of_nonneg_left hnorm (abs_nonneg (a - b))]
    _ = _ := by simp

theorem norm_charFun_sub_le_of_unit_support (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) (a b : ℝ) :
    ‖charFun μ a - charFun μ b‖ ≤ |a - b| := by
  simpa only [one_mul] using norm_charFun_sub_le_of_support μ hsupp a b

theorem one_half_le_norm_charFun_uniformNoise {r R : ℝ} (hr : 0 < r)
    (hRr : r * R ≤ 1 / 2) {v : ℝ} (hv : |v| ≤ R) :
    1 / 2 ≤ ‖charFun (uniformNoise r) v‖ := by
  let : IsProbabilityMeasure (uniformNoise r) := uniformNoise_probability hr
  have h : ‖charFun (uniformNoise r) v - 1‖ ≤ r * |v| := by
    simpa using norm_charFun_sub_le_of_support (uniformNoise r) (uniformNoise_support r) v 0
  have hnorm : ‖(1 : ℂ)‖ - ‖charFun (uniformNoise r) v‖ ≤
      ‖charFun (uniformNoise r) v - 1‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le (1 : ℂ) (charFun (uniformNoise r) v)
  have hbound := mul_le_mul_of_nonneg_left hv hr.le
  norm_num at hnorm
  linarith

theorem charFun_sq_le_charFun_sq_add (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) (a b : ℝ) :
    ‖charFun μ a‖ ^ 2 ≤ ‖charFun μ b‖ ^ 2 + 2 * |a - b| := by
  have ha := norm_charFun_le_one (μ := μ) a
  have hb := norm_charFun_le_one (μ := μ) b
  have hdiff : |‖charFun μ a‖ - ‖charFun μ b‖| ≤ |a - b| :=
    (abs_norm_sub_norm_le _ _).trans (norm_charFun_sub_le_of_unit_support μ hsupp a b)
  have hsum0 : 0 ≤ ‖charFun μ a‖ + ‖charFun μ b‖ := by positivity
  have hsum1 : ‖charFun μ a‖ + ‖charFun μ b‖ ≤ 2 := by linarith
  have hdiffsq : ‖charFun μ a‖ ^ 2 - ‖charFun μ b‖ ^ 2 ≤ 2 * |a - b| := by
    calc _ = (‖charFun μ a‖ - ‖charFun μ b‖) * (‖charFun μ a‖ + ‖charFun μ b‖) := by ring
      _ ≤ |‖charFun μ a‖ - ‖charFun μ b‖| * (‖charFun μ a‖ + ‖charFun μ b‖) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
      _ ≤ |a - b| * 2 := mul_le_mul hdiff hsum1 hsum0 (abs_nonneg _)
      _ = _ := by ring
  linarith

theorem integrable_charFun_sq_comp (α η : Measure ℝ)
    [IsProbabilityMeasure α] [IsProbabilityMeasure η] (q : ℝ) :
    Integrable (fun x => ‖charFun α (q * x)‖ ^ 2) η := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := norm_charFun_le_one (μ := α) (q * x)
  nlinarith [norm_nonneg (charFun α (q * x))]

/-- Moving the sampling measure by noise of radius `δ` changes the averaged
characteristic-function square by at most `2*|q|*δ`. -/
theorem charFun_sq_integral_le_uniform_smoothing (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hsupp : α (Icc (-1 : ℝ) 1)ᶜ = 0) {δ : ℝ} (hδ : 0 < δ) (q : ℝ) :
    (∫ x, ‖charFun α (q * x)‖ ^ 2 ∂β) ≤
      (∫ x, ‖charFun α (q * x)‖ ^ 2 ∂(β ∗ uniformNoise δ)) + 2 * |q| * δ := by
  let : IsProbabilityMeasure (uniformNoise δ) := uniformNoise_probability hδ
  let F : ℝ → ℝ := fun x => ‖charFun α (q * x)‖ ^ 2
  have hF0 (x : ℝ) : 0 ≤ F x := sq_nonneg _
  have hF1 (x : ℝ) : F x ≤ 1 := by
    have h := norm_charFun_le_one (μ := α) (q * x)
    dsimp [F]
    nlinarith [norm_nonneg (charFun α (q * x))]
  have hFint (η : Measure ℝ) [IsProbabilityMeasure η] : Integrable F η :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 x)] using hF1 x)
  have hinner (x : ℝ) : F x ≤ (∫ z, F (x + z) ∂(uniformNoise δ)) + 2 * |q| * δ := by
    have hint : Integrable (fun z => F (x + z)) (uniformNoise δ) :=
      (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 _)] using hF1 (x + z))
    calc F x = ∫ _z, F x ∂(uniformNoise δ) := by simp
      _ ≤ ∫ z, F (x + z) + 2 * |q| * δ ∂(uniformNoise δ) := by
        apply integral_mono_ae (integrable_const _) (hint.add (integrable_const _))
        filter_upwards [mem_ae_iff.mpr (uniformNoise_support δ)] with z hz
        have hb := charFun_sq_le_charFun_sq_add α hsupp (q * x) (q * (x + z))
        have habs : |q * x - q * (x + z)| ≤ |q| * δ := by
          rw [show q * x - q * (x + z) = -(q * z) by ring, abs_neg, abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_le.mpr hz) (abs_nonneg _)
        dsimp [F]
        linarith
      _ = _ := by rw [integral_add hint (integrable_const _)]; simp
  have hJ : Integrable (fun x => ∫ z, F (x + z) ∂(uniformNoise δ)) β := by
    have h := ((integrable_conv_iff (hFint (β ∗ uniformNoise δ)).aestronglyMeasurable).mp
      (hFint (β ∗ uniformNoise δ))).2
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 _)] using h
  rw [integral_conv (hFint (β ∗ uniformNoise δ))]
  calc
    _ ≤ ∫ x, (∫ z, F (x + z) ∂(uniformNoise δ)) + 2 * |q| * δ ∂β := by
      exact integral_mono (hFint β) (hJ.add (integrable_const _)) hinner
    _ = _ := by rw [integral_add hJ (integrable_const _)]; simp

end Submission.Obl.k4_oss_flat_decay
