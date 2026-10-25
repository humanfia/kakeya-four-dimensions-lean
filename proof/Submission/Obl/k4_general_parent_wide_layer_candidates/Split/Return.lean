import Submission.Obl.k4_general_parent_wide_layer_candidates.ComparedClosure
import Submission.Obl.k4_general_parent_wide_layer_candidates.Confine.Deep

namespace Submission.Obl.k4_general_parent_wide_layer_candidates.Split

/-- Native confinement is proved from the original data; it is no longer
a proposed child of this split. -/
theorem nativeConfinement_proved : NativeConfinementCore := by
  intro α _ p hp
  exact ⟨deepMultiplier p.κ p.ℓ, hp.deepConfinement.1, hp.deepConfinement.2⟩

/-- The two analytic children close the parent through the checked downstream
geometry, Scalar application, calibration and original-mass return. -/
theorem core_of_compared_children
    (hcompare : ComparedLayerCore) (hlists : ComparedListCore) : Core :=
  core_of_compared_layers hcompare hlists nativeConfinement_proved

end Submission.Obl.k4_general_parent_wide_layer_candidates.Split
