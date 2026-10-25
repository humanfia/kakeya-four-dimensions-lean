-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.CountablePositiveStateCut, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch.ResamplingRatio

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

/-- Null countable cells can be removed as whole cells, with exactly
zero measure loss. Every remaining nonempty cell has positive mass. -/
theorem exists_positive_whole_state_source {Ω Code : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Code] [Countable Code] [MeasurableSingletonClass Code]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (hsupport : ∀ᵐ z ∂μ, z∈E) (state : Ω → Code) (hstate : Measurable state) :
    ∃ U : Set Code, MeasurableSet U ∧
      MeasurableSet (E∩state ⁻¹' U) ∧ μ.restrict (E∩state ⁻¹' U)=μ ∧
      ∀ z∈E∩state ⁻¹' U,
        0<μ.real ((E∩state ⁻¹' U)∩state ⁻¹' {state z}) := by
  let U := {q : Code | μ (state ⁻¹' {q})≠0}
  have hU : MeasurableSet U := (to_countable U).measurableSet
  have hkeep : MeasurableSet (E∩state ⁻¹' U) := hE.inter (hstate hU)
  have hfull : ∀ᵐ z ∂μ, z∈E∩state ⁻¹' U := by
    filter_upwards [hsupport,Switch.ae_state_mass_ne_zero μ state] with z hz hmass
    exact ⟨hz,hmass⟩
  have hrestrict : μ.restrict (E∩state ⁻¹' U)=μ := Measure.restrict_eq_self_of_ae_mem hfull
  refine ⟨U,hU,hkeep,hrestrict,?_⟩
  intro z hz
  have hmass : μ (((E∩state ⁻¹' U)∩state ⁻¹' {state z}))=μ (state ⁻¹' {state z}) := by
    rw [inter_comm,←Measure.restrict_apply (hstate (measurableSet_singleton (state z))),hrestrict]
  rw [measureReal_def,hmass]
  exact ENNReal.toReal_pos hz.2 (measure_ne_top μ _)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
