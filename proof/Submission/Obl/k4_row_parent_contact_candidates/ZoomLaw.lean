import Submission.Obl.k4_general_parent_projected_layers.Support.ZoomLaw

/-! Reuse the accepted parent laws; add transfer of measurable a.e. predicates.
The additional lemma is adapted from here:o222, x0776, commit 0a43f16b. -/

namespace Submission.Obl.k4_row_parent_contact_candidates

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α]

export Submission.Obl.k4_general_parent_projected_layers
  (zoomTime measurable_zoomTime condPrior condPrior_apply condPrior_isProbability
   zoomLaw zoomLaw_apply zoomLaw_univ zoomLaw_mono_set zoomLaw_mono_measure
   zoomLaw_compl_unit zoomLaw_le)

/-- Almost-everywhere statements transfer to the zoomed law. -/
theorem ae_zoomLaw (μ₀ : Measure (α × ℝ)) {S : Set (α × ℝ)} (hS : MeasurableSet S)
    (t₀ q : ℝ) (W : ℝ≥0∞) {P : α × ℝ → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ᵐ z ∂μ₀, z ∈ S → P (zoomTime t₀ q z)) :
    ∀ᵐ z ∂zoomLaw μ₀ S t₀ q W, P z := by
  unfold zoomLaw
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_zoomTime t₀ q).aemeasurable hP, ae_restrict_iff' hS]
  exact h

end

end Submission.Obl.k4_row_parent_contact_candidates
