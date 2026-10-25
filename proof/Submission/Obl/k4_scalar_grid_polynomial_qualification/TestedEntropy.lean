import Submission.Obl.k4_scalar_grid_polynomial_qualification.Entropy

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Entropy

open Set MeasureTheory ProbabilityTheory

theorem integrable_unit_function {T : Type*} [MeasurableSpace T]
    (ν : Measure T) [IsFiniteMeasure ν] {s : T → ℝ} (hs : Measurable s)
    (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1) : Integrable s ν := by
  apply Integrable.of_bound hs.aestronglyMeasurable 1
  exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hs0 t)] using hs1 t)

theorem integrable_negMulLog_unit {T : Type*} [MeasurableSpace T]
    (ν : Measure T) [IsFiniteMeasure ν] {s : T → ℝ} (hs : Measurable s)
    (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1) :
    Integrable (fun t => Real.negMulLog (s t)) ν := by
  apply Integrable.of_bound (Real.continuous_negMulLog.measurable.comp hs).aestronglyMeasurable 1
  apply ae_of_all
  intro t
  change ‖Real.negMulLog (s t)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg (hs0 t) (hs1 t))]
  exact (Real.negMulLog_le_one_sub_self (hs0 t)).trans (by linarith [hs0 t])

/-- Jensen's denominator bound uses the actual total success mass, even
when some individual conditional success probabilities are arbitrarily
small. The base variable may contain continuous times and coefficient bins. -/
theorem denominator_entropy {T : Type*} [MeasurableSpace T]
    (ν : Measure T) [IsProbabilityMeasure ν] {s : T → ℝ} (hs : Measurable s)
    (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hp : 0 < ∫ t, s t ∂ν) :
    (∫ t, Real.negMulLog (s t) ∂ν) / (∫ t, s t ∂ν) ≤
      Real.log (∫ t, s t ∂ν)⁻¹ := by
  have h := Real.concaveOn_negMulLog.le_map_integral
    Real.continuous_negMulLog.continuousOn isClosed_Ici
    (ae_of_all _ hs0) (integrable_unit_function ν hs hs0 hs1)
    (integrable_negMulLog_unit ν hs hs0 hs1)
  apply (div_le_iff₀ hp).2
  exact h.trans_eq (by rw [Real.negMulLog, Real.log_inv]; ring)

theorem measurable_kernel_entropy {T S : Type*}
    [MeasurableSpace T] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    (κ : Kernel T S) [IsMarkovKernel κ] : Measurable (fun t => measureEntropy (κ t)) := by
  simp only [measureEntropy_of_isProbabilityMeasure, tsum_fintype]
  apply Finset.measurable_sum
  intro s _
  exact Real.continuous_negMulLog.measurable.comp
    ((κ.measurable_coe (measurableSet_singleton s)).ennreal_toReal)

theorem integrable_success_entropy {T S : Type*}
    [MeasurableSpace T] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    (ν : Measure T) [IsFiniteMeasure ν] (κ : Kernel T S) [IsMarkovKernel κ]
    {s : T → ℝ} (hs : Measurable s) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1) :
    Integrable (fun t => s t * measureEntropy (κ t)) ν := by
  apply Integrable.of_bound
    (hs.mul (measurable_kernel_entropy κ)).aestronglyMeasurable (Real.log (Fintype.card S))
  apply ae_of_all
  intro t
  change ‖s t * measureEntropy (κ t)‖ ≤ Real.log (Fintype.card S)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hs0 t) (measureEntropy_nonneg _))]
  exact (mul_le_of_le_one_left (measureEntropy_nonneg _) (hs1 t)).trans
    (measureEntropy_le_log_card _)

/-- An original atom cap loses only the logarithm of the total event mass
after restriction. This is the continuous-conditioning calculation in the
dense-tested-event entropy lemma. -/
theorem tested_entropy_lower_bound {T S : Type*}
    [MeasurableSpace T] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    (ν : Measure T) [IsProbabilityMeasure ν] (κ : Kernel T S) [IsMarkovKernel κ]
    {s : T → ℝ} (hs : Measurable s) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hp : 0 < ∫ t, s t ∂ν) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ t, 0 < s t → ∀ a, (κ t).real {a} ≤ c / s t) :
    -Real.log c - Real.log (∫ t, s t ∂ν)⁻¹ ≤
      (∫ t, s t * measureEntropy (κ t) ∂ν) / (∫ t, s t ∂ν) := by
  have hpoint (t : T) :
      -(s t * Real.log c) - Real.negMulLog (s t) ≤ s t * measureEntropy (κ t) := by
    by_cases hz : s t = 0
    · simp [hz]
    have hst : 0 < s t := lt_of_le_of_ne (hs0 t) (Ne.symm hz)
    have h := mul_le_mul_of_nonneg_left
      (entropy_lower_bound_of_atom_bound (κ t) (div_pos hc hst) (hcap t hst)) (hs0 t)
    rw [Real.log_div hc.ne' hz] at h
    dsimp only [Real.negMulLog]
    nlinarith only [h]
  have hsI := integrable_unit_function ν hs hs0 hs1
  have hnI := integrable_negMulLog_unit ν hs hs0 hs1
  have hi := integral_mono ((hsI.mul_const (Real.log c)).neg.sub hnI)
    (integrable_success_entropy ν κ hs hs0 hs1) hpoint
  change (∫ t, -(s t * Real.log c) - Real.negMulLog (s t) ∂ν) ≤
    (∫ t, s t * measureEntropy (κ t) ∂ν) at hi
  rw [integral_sub (f := fun t => -(s t * Real.log c))
    (g := fun t => Real.negMulLog (s t)) (hsI.mul_const (Real.log c)).neg hnI, integral_neg,
    integral_mul_const] at hi
  have hj := denominator_entropy ν hs hs0 hs1 hp
  apply (le_div_iff₀ hp).2
  have hj' := (div_le_iff₀ hp).1 hj
  nlinarith

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Entropy
