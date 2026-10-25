import Submission.Obl.k4_finite_affine_parent_sources.FrozenBridge
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionMain

/-!
# The frozen affine-parent source assertion from per-sample selection

The geometric component and the outer parameter schedule are supplied by the
existing source-preparation closure. Only the actual simultaneous per-sample
selection remains an input; both observations and all original-prior source
fields remain in the conclusion.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

/-- The frozen statement of o279 follows from the per-sample selection. -/
theorem flat_of_sample (h : SelectionSample) : FlatSourcePreparation :=
  flat_of_selection (sourceSelectionSpec_of_sample h)

end Submission.Obl.k4_finite_affine_parent_sources
