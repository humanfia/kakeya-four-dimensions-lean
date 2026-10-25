import Submission.Obl.k4_scalar_guarded_entropic_path.CandidateAssembly
import Submission.Obl.k4_scalar_guarded_entropic_path.StageInformation
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageSelection

/-! Intersect the all-candidate tails before selecting one original
sample and its information window. All selected data come from that
single common prepared law. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

/-- The concrete geometric and information constructions close the
stage once the predeclared density menu gives its reference inputs on
the same all-candidate tail. -/
theorem exists_good_stage_of_reference_inputs
    (s : StagePath ctx source k R δ) (al : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ al.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent)
    (htol : ∀ a, (base a).tolerance = pe.τ)
    (hR : 1 < R) (hκ : 0 < ctx.κ) (hκ1 : ctx.κ ≤ 1)
    (hη : 0 < ctx.η) (hδ : δ ≤ 1)
    (href : ∀ᶠ j in atTop, ∀ (a : Fin s.layout.L)
      (node : ℝ → Fin (s.views (s.candidateIndex a)).count)
      (layers : Fin (s.views (s.candidateIndex a)).count →
        Layer (W (s.views (s.candidateIndex a)).parent
          ((s.views (s.candidateIndex a)).suffixChain.sample j))) (α : ℝ),
      ∃ (ε : ℝ) (us : Finset ℝ),
        Reference.CandidateInput (s.candidateStage al pe base j a node layers α)
          ctx.dstar (min ctx.S₀ 1) R (s.graphK j) s.layout.m ε pe.τ pe.γ us) :
    ∃ st : RawStage, st.Good ctx.dstar ctx.κ (min ctx.S₀ 1) k R δ := by
  have hgeometry := s.eventually_candidate_geometry hR hη al pe base htol
  have hcost := s.layout.eventually_window_cost s.tangentN s.tangentN_tendsto
  have hwindow := s.eventually_window_selection al pe base htol hκ hκ1 hη hδ hcost
  obtain ⟨j, hgj, hrj, hwj⟩ := (hgeometry.and (href.and hwindow)).exists
  obtain ⟨sel⟩ := hwj
  obtain ⟨node, layers, hgood⟩ := hgj sel.index
  obtain ⟨ε, us, hreference⟩ := hrj sel.index node layers sel.α
  exact s.exists_good_stage_of_selected_candidate al pe base j sel.index node layers
    (hgood (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m) sel.α)
    hreference sel.alpha_pos sel.alpha_two sel.alpha_le sel.score

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
