-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CurrentPaletteRealDomination, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockIncidenceCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped ENNReal BigOperators

/-- Extended-real current palette ratios give the real-valued fiber
ratios used by physical row regularity. The source law is unchanged. -/
theorem real_state_domination_of_current_caps {Ω Code Velocity : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Velocity]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω)
    (hfull : ∀ᵐ z ∂μ, z∈E) (state : Ω → Code) (velocity : Ω → Velocity)
    (palette : Measure Velocity) [IsFiniteMeasure palette]
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ q v, μ {z | state z=q ∧ velocity z=v} ≤
      ENNReal.ofReal C*μ (state ⁻¹' {q})*palette {v}) :
    ∀ z∈E, ∀ v, μ.real (E∩state ⁻¹' {state z}∩{x | velocity x=v}) ≤
      C*μ.real (E∩state ⁻¹' {state z})*(palette {v}).toReal := by
  have hinter (A : Set Ω) : μ.real (E∩A)=μ.real A := by
    apply measureReal_congr
    filter_upwards [hfull] with z hz
    simp only [mem_inter_iff,hz,true_and]
  intro z _ v
  rw [inter_assoc,hinter,hinter]
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _))
      (measure_ne_top palette _)) (hcap (state z) v)
  have hset : state ⁻¹' {state z}∩{x | velocity x=v}={x | state x=state z ∧ velocity x=v} := by
    ext x
    simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
  rw [hset]
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal hC] using hh

/-- Every finite list of atoms has total weight at most one in the
same original probability palette. -/
theorem probability_palette_sum_le_one {Velocity : Type*} [MeasurableSpace Velocity]
    [MeasurableSingletonClass Velocity] (palette : Measure Velocity) [IsProbabilityMeasure palette]
    (bins : Finset Velocity) : ∑ v∈bins, (palette {v}).toReal ≤ 1 := by
  change ∑ v∈bins, palette.real {v} ≤ 1
  rw [sum_measureReal_singleton]
  calc
    _ ≤ palette.real univ := measureReal_mono (subset_univ _)
    _ = 1 := by simp [measureReal_def]

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
