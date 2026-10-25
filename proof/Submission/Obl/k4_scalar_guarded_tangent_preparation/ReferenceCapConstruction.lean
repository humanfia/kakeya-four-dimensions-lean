import Submission.Obl.k4_scalar_guarded_tangent_preparation.Construction
import Submission.Obl.k4_scalar_guarded_tangent_preparation.ReferenceCapsProof

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

/-- The measured finite-reference preparation is independent of the
geometric realization and full-prior completion. -/
theorem referenceCapPreparation : ReferenceCapPreparation := by
  intro N B d S W ω σ h
  exact prepare_reference_caps N B d S W ω σ h

end Submission.Obl.k4_scalar_guarded_tangent_preparation
