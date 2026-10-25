import Submission.Obl.k4_matching_switching_target_certificate.TargetConstruction
import Submission.Obl.k4_matching_switching_target_certificate.Interfaces

namespace Submission.Obl.k4_matching_switching_target_certificate

/-- The complete deterministic cover in the original frozen coordinates. -/
theorem geometricCover : GeometricCoverStatement :=
  geometricCover_of_targetConstruction targetConstruction

end Submission.Obl.k4_matching_switching_target_certificate
