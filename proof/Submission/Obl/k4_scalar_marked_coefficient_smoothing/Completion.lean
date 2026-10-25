import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Assembly
import Submission.Obl.k4_scalar_marked_terminal_support

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

/-- The geometric support child follows from the explicit finite support cover. -/
theorem terminal_support_claim : SupportTransferClaim :=
  Submission.k4_scalar_marked_terminal_support

/-- Only the fixed-sample density transfer remains after the proved finite and
geometric constructions. -/
theorem smoothing_of_density (hdensity : DensityTransferClaim) : SmoothingStatement :=
  smoothing_of_analytic_children hdensity terminal_support_claim

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
