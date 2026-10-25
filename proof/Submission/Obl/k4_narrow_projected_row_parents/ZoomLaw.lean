/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/Renewal/ZoomLaw.lean.
   The original proof was adapted there from o222, session x0776, commit 6141c018. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ZoomLaw

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers

variable {α : Type*} [MeasurableSpace α]

/-- Almost-everywhere statements transfer to a normalized parent law. -/
theorem ae_zoomLaw (μ₀ : Measure (α × ℝ)) {S : Set (α × ℝ)} (hS : MeasurableSet S)
    (t₀ q : ℝ) (W : ℝ≥0∞) {P : α × ℝ → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ᵐ z ∂μ₀, z ∈ S → P (zoomTime t₀ q z)) :
    ∀ᵐ z ∂zoomLaw μ₀ S t₀ q W, P z := by
  unfold zoomLaw
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_zoomTime t₀ q).aemeasurable hP, ae_restrict_iff' hS]
  exact h

end Submission.Obl.k4_narrow_projected_row_parents
