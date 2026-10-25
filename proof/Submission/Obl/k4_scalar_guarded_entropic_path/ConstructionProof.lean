import Submission.Obl.k4_scalar_guarded_entropic_path.EntropicFromCriticalStages
import Submission.Obl.k4_scalar_guarded_entropic_path.FiniteStageSelection
import Submission.Obl.k4_scalar_guarded_entropic_path.Reference.StageCore

/-! Construct every finite stage from the genuine critical path, the
common density menu and its selected original information window, then
apply the checked stage diagonal. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open PathGeometry.PathNodes

noncomputable section

theorem entropicPathConstruction : EntropicPathConstruction := by
  apply entropicPathConstruction_of_critical_stages
  intro ctx source hlength hcalc hκ hκ1 hη hS k R δ hR hδ hδ1
  obtain ⟨s⟩ := nonempty_stagePath source hlength hcalc hκ hη k hR hδ
  obtain ⟨al⟩ := nonempty_stageAllowances s hκ
  obtain ⟨pe⟩ := nonempty_preparationExponents s.layout.scale_pos hδ al.v_pos hS hη
  exact s.exists_good_stage_of_reference_inputs al pe (s.referenceTests pe)
    (fun _ => rfl) hR hκ hκ1 hη hδ1 (s.eventually_reference_inputs al pe hR hη)

end

end Submission.Obl.k4_scalar_guarded_entropic_path
