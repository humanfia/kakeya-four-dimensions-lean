import Submission.Obl.k4_scalar_guarded_tangent_preparation.Assembly
import Submission.Obl.k4_scalar_guarded_tangent_preparation.ReferenceCapConstruction
import Submission.Obl.k4_scalar_guarded_tangent_preparation.Completion

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

/-- Only genuine guarded entropic paths remain to construct. Cap transfer
and full-prior layer completion are the concrete proved components. -/
theorem preparation_of_entropic_path
    (hI : Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Initial)
    (hC : Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Calculus)
    (hpath : EntropicPathConstruction) :
    Submission.Obl.k4_scalar_linear_critical_extremizers.Split.Critical → GuardedPrepared :=
  assemble hI hC hpath referenceCapPreparation fullPriorLayerCompletion

end Submission.Obl.k4_scalar_guarded_tangent_preparation
