import Submission.Obl.k4_horizontal_coefficient_count.HeavyTail
import Submission.Obl.k4_horizontal_coefficient_count.Model
import Submission.Obl.k4_horizontal_coefficient_count.SupportCount
import Submission.Obl.k4_horizontal_coefficient_count.LMAsymptotic

namespace Submission.Obl.k4_horizontal_coefficient_count

/-- At every fixed admissible depth, scalar clustering discards only a
power-decaying mass of light coefficient cells. -/
theorem rawEngine : RawEngine := by
  intro α mα cfg h s hs hsU hse ε hε
  refine heavyCoverAt_of_light_tail cfg.N cfg.K h.scale h.scale_limit h.subpower.1
    h.subpower.2 cfg.d cfg.e₀ s ε hε cfg.ρ cfg.π cfg.b
    (fun k => (h.basic k).1) h.residual_time ?_ ?_
  · exact eventually_goodSet_conull cfg h.subpower.1 h.basic h.atlas hs (by linarith)
  · exact light_mass_eventually cfg h.scale h.scale_limit h.subpower.1 h.subpower.2
      h.dimension_nonneg h.dimension_lt_one h.rate_pos h.subcritical_rate h.horizontal_rate
      h.defect_pos h.basic h.caps h.atlas 6442450944 17 supportCount_of_hyp hs
      (by linarith) (by linarith) (by positivity : 0 < ε / 2)

end Submission.Obl.k4_horizontal_coefficient_count
