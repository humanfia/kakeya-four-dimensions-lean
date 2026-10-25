import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_adapted_oscillation_tests

/-- On a probability space, pairwise oscillation controls the excess of the
absolute integral over the absolute mean. -/
theorem integral_abs_sub_abs_integral_le_pairwise
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) :
    (∫ x, |f x| ∂μ) - |∫ x, f x ∂μ| ≤
      ∫ x, ∫ y, |f x - f y| ∂μ ∂μ := by
  have hd : Integrable (fun p : α × α => |f p.1 - f p.2|) (μ.prod μ) :=
    ((hf.comp_fst μ).sub (hf.comp_snd μ)).abs
  have hx (x : α) : |f x| - |∫ y, f y ∂μ| ≤ ∫ y, |f x - f y| ∂μ := by
    refine (abs_sub_abs_le_abs_sub _ _).trans ?_
    have heq : (∫ y, f x - f y ∂μ) = f x - ∫ y, f y ∂μ := by
      rw [integral_sub (integrable_const _) hf]
      simp
    rw [← heq]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun y => f x - f y) (μ := μ)
  have h := integral_mono (hf.abs.sub (integrable_const _)) hd.integral_prod_left hx
  change (∫ x, |f x| - |∫ y, f y ∂μ| ∂μ) ≤
    ∫ x, ∫ y, |f x - f y| ∂μ ∂μ at h
  rw [integral_sub hf.abs (integrable_const _)] at h
  simpa using h

/-- The normalized oscillation tests force pairwise oscillation at least one half. -/
theorem half_le_pairwise_of_tests
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ)
    (hmean : |∫ x, f x ∂μ| ≤ 1 / 2)
    (habs : 1 ≤ ∫ x, |f x| ∂μ) :
    1 / 2 ≤ ∫ x, ∫ y, |f x - f y| ∂μ ∂μ := by
  have h := integral_abs_sub_abs_integral_le_pairwise hf
  linarith

/-- Convert a nonnegative cube oscillation bound from lower integrals to real integrals. -/
theorem pairwise_integral_le_sum_of_lintegral_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {f : α → ℝ} (hf : Integrable f μ)
    (F : ι → α → ℝ) (hF : ∀ i, Integrable (F i) μ) (hFpos : ∀ i x, 0 ≤ F i x)
    (hbound : (∫⁻ p : α × α, ENNReal.ofReal |f p.1 - f p.2| ∂μ.prod μ) ≤
      ∑ i, ∫⁻ x, ENNReal.ofReal (F i x) ∂μ) :
    (∫ x, ∫ y, |f x - f y| ∂μ ∂μ) ≤ ∑ i, ∫ x, F i x ∂μ := by
  have hpair : Integrable (fun p : α × α => |f p.1 - f p.2|) (μ.prod μ) :=
    ((hf.comp_fst μ).sub (hf.comp_snd μ)).abs
  have hfin (i : ι) : (∫⁻ x, ENNReal.ofReal (F i x) ∂μ) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hF i)
      (Filter.Eventually.of_forall (hFpos i))]
    exact ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun i hi => hfin i)) hbound
  rw [ENNReal.toReal_sum (fun i hi => hfin i)] at hreal
  have hleft :
      (∫⁻ p : α × α, ENNReal.ofReal |f p.1 - f p.2| ∂μ.prod μ).toReal =
      ∫ x, ∫ y, |f x - f y| ∂μ ∂μ := by
    rw [← integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun p : α × α => abs_nonneg (f p.1 - f p.2))
      hpair.aestronglyMeasurable]
    exact integral_prod _ hpair
  rw [hleft] at hreal
  have hright (i : ι) : (∫⁻ x, ENNReal.ofReal (F i x) ∂μ).toReal = ∫ x, F i x ∂μ :=
    (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hFpos i))
      (hF i).aestronglyMeasurable).symm
  simpa only [hright] using hreal

end Submission.Obl.k4_adapted_oscillation_tests
