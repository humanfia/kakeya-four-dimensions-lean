import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.Interface
import Submission.Lib.K4ExactProblemOps.Coarsening

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

theorem measurable_obs (B a : ℝ) : Measurable (obs B a) :=
  Submission.Lib.K4ExactProblemOps.measurable_obs B a

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
