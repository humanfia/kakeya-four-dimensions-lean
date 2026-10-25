-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/MeasurableCore.lean
import Mathlib.MeasureTheory.Measure.Restrict

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Set MeasureTheory

/-- Arbitrary original null exceptions can be removed using one measurable
conull core, before defining the restricted original candidate laws. -/
theorem exists_measurable_conull_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : Set Ω) (hG : ∀ᵐ u ∂μ, u ∈ G) :
    ∃ C : Set Ω, MeasurableSet C ∧ C ⊆ G ∧ ∀ᵐ u ∂μ, u ∈ C := by
  refine ⟨(toMeasurable μ Gᶜ)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · simpa only [compl_compl] using compl_subset_compl.mpr (subset_toMeasurable μ Gᶜ)
  · apply ae_iff.mpr
    change μ ((toMeasurable μ Gᶜ)ᶜ)ᶜ = 0
    rw [compl_compl, measure_toMeasurable]
    exact ae_iff.mp hG

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
