import Submission.Obl.k4_scalar_normalized_exact_refinement.Interfaces
import Submission.Obl.k4_scalar_normalized_exact_refinement.Profile

/-!
# The relative-profile stage

`Stages.RelativeProfiles` from `Analysis.RefData.relative_profiles`.
-/

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

theorem relativeProfiles_stage : Stages.RelativeProfiles := by
  intro p q r b h hp hqraw hqpure hr _hrL _hrb hbL hLq href
  obtain ⟨R⟩ := RefData.nonempty (p := p) (q := q) (r := r) (b := b) (h := h) href
  exact R.relative_profiles hp hqraw hqpure hr hbL hLq

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
