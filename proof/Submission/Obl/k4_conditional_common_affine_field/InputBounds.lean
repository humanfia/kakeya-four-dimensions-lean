import Submission.Obl.k4_horizontal_supercritical_three_projections.FamilyMass

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal

/-- The unit-time density bound controls the original total mass. -/
theorem original_mass_upper {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ)) (K : ℝ)
    (hdom : μ ≤ ENNReal.ofReal K • ν.prod volume)
    (htime : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) : μ univ ≤ ENNReal.ofReal K := by
  have h := Submission.Obl.k4_horizontal_supercritical_three_projections.incidence_assignment_bound
    ν μ univ (ENNReal.ofReal K) hdom htime
  simpa only [mem_univ,Set.ofPred_true,measure_univ,mul_one] using h

theorem original_measure_finite {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ)) (K : ℝ)
    (hdom : μ ≤ ENNReal.ofReal K • ν.prod volume)
    (htime : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) : IsFiniteMeasure μ :=
  ⟨(original_mass_upper ν μ K hdom htime).trans_lt ENNReal.ofReal_lt_top⟩

end Submission.Obl.k4_conditional_common_affine_field
