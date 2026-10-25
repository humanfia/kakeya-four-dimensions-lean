import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageAllowances
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageCore
import Submission.Obl.k4_scalar_guarded_entropic_path.StageEnvelope

/-! One inner tail pays every candidate's actual logarithmic allowance,
coefficient and row budgets, and unchanged-original-law mass reserve. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

theorem view_K_subpower (s : StagePath ctx source k R δ) (a : s.ViewIndex)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, K (s.views a).parent ((s.views a).suffixChain.sample j) ≤ N s.final j ^ ε := by
  filter_upwards [(s.views a).suffixChain.sample_strictMono.tendsto_atTop.eventually
    ((s.views a).parent_exact.1.2.2.1.2 ε hε)] with j hj
  rw [← s.views_resolution a j]
  exact hj

theorem eventually_power_envelopes (s : StagePath ctx source k R δ) (hη : 0 < ctx.η)
    (allow : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ allow.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent) :
    ∀ᶠ j in atTop, ∀ a : s.ViewIndex,
      PowerEnvelope (N s.final j) (K (s.views a).parent ((s.views a).suffixChain.sample j))
        (∑ g, ENNReal.ofReal (ω (s.views a).parent ((s.views a).suffixChain.sample j) g) *
          s.worldLaw pe base j a g univ) k (s.views a).count allow.M₀ s.layout.scale allow.v δ := by
  have hscale := s.layout.scale_pos
  have hδ : 0 < δ := hscale.trans_le s.layout.scale_error
  have hbudget : ((k + 1 : ℕ) : ℝ) * allow.v < s.layout.scale * δ := by
    linarith only [allow.power_budget, mul_pos hscale hδ]
  apply Filter.eventually_all.2
  intro a
  apply eventually_powerEnvelope (N s.final)
    (fun j => K (s.views a).parent ((s.views a).suffixChain.sample j))
    s.final_exact.1.1 s.final_exact.1.2.1 (s.view_K_subpower a)
    (fun j => ∑ g, ENNReal.ofReal (ω (s.views a).parent ((s.views a).suffixChain.sample j) g) *
      s.worldLaw pe base j a g univ)
    (fun ε hε => (s.worldLaw_mass_subpower hη pe base ε hε).mono fun j hj => hj a)
    k (s.views a).count allow.M₀ allow.M_one hscale allow.v_pos allow.v_one hδ hbudget

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
