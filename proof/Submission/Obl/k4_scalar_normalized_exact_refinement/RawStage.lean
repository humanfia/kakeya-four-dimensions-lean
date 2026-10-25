import Submission.Obl.k4_scalar_normalized_exact_refinement.Interfaces
import Submission.Obl.k4_scalar_normalized_exact_refinement.RawRefinement

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

theorem raw_refinement_stage : Stages.RawRefinement := by
  intro p r b h d' hp hr hrL _ _ hd hd1 hk
  exact raw_normalized_refinement p r b h d' hp hr hrL hd hd1 hk

end Submission.Obl.k4_scalar_normalized_exact_refinement
