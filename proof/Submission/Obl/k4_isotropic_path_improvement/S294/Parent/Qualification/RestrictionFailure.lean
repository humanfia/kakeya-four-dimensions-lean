-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.RestrictionFailure, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped ENNReal

/-- Control need only be constructed on a hypothetical failure subset.
Its selection loss multiplies the analytic failure estimate, and the
original physical source need never be replaced by that selection. -/
theorem failure_mass_le_of_controlled_subselection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E good : Set Ω) (hE : MeasurableSet E) (hgood : MeasurableSet good)
    (control : Set Ω → Prop) (factor loss eta : ENNReal)
    (hselection : ∀ U : Set Ω, MeasurableSet U → U⊆E →
      ∃ S : Set Ω, MeasurableSet S ∧ S⊆U ∧ μ U≤factor*μ S+loss ∧ control S)
    (hqualified : ∀ S : Set Ω, MeasurableSet S → S⊆E → control S → μ (S\good)≤eta) :
    μ (E\good)≤factor*eta+loss := by
  obtain ⟨S,hS,hSbad,hmass,hcontrol⟩ := hselection (E\good) (hE.diff hgood) sdiff_subset
  have hdisjoint : S\good=S := by
    ext z
    constructor
    · exact fun hz => hz.1
    · exact fun hz => ⟨hz,(hSbad hz).2⟩
  have hbound := hqualified S hS (hSbad.trans sdiff_subset) hcontrol
  rw [hdisjoint] at hbound
  exact hmass.trans (add_le_add (mul_le_mul' le_rfl hbound) le_rfl)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
