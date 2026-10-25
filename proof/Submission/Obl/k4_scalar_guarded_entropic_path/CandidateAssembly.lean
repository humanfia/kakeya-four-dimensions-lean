import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageCoreGeometry
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageObservations
import Submission.Obl.k4_scalar_guarded_entropic_path.Reference.Stage
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.CanonicalScore

/-! Assemble a selected window on its literal original parent and
sample. The reference fields use the same common canonical resolution
and graph box as the entropy estimate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

def candidateStage (s : StagePath ctx source k R δ) (al : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ al.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent)
    (j : ℕ) (a : Fin s.layout.L)
    (node : ℝ → Fin (s.views (s.candidateIndex a)).count)
    (layers : Fin (s.views (s.candidateIndex a)).count →
      Layer (W (s.views (s.candidateIndex a)).parent
        ((s.views (s.candidateIndex a)).suffixChain.sample j))) (α : ℝ) : RawStage :=
  (s.views (s.candidateIndex a)).toRawStage j s.layout.scale
    (Code.N (s.views (s.candidateIndex a)).parent
      ((s.views (s.candidateIndex a)).suffixChain.sample j) ^ al.v)
    (δ / 1000)
    (Code.N (s.views (s.candidateIndex a)).parent
      ((s.views (s.candidateIndex a)).suffixChain.sample j) ^ (s.layout.scale * δ))
    al.M₀ pe.ε (s.coreSet pe base j) node layers s.layout.m
    (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m) α

theorem candidateStage_resolution (s : StagePath ctx source k R δ) (al : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ al.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent)
    (j : ℕ) (a : Fin s.layout.L)
    (node : ℝ → Fin (s.views (s.candidateIndex a)).count)
    (layers : Fin (s.views (s.candidateIndex a)).count →
      Layer (W (s.views (s.candidateIndex a)).parent
        ((s.views (s.candidateIndex a)).suffixChain.sample j))) (α : ℝ) :
    (s.candidateStage al pe base j a node layers α).N = s.tangentN j := by
  change Code.N (s.views (s.candidateIndex a)).parent
    ((s.views (s.candidateIndex a)).suffixChain.sample j) ^ s.layout.scale = _
  exact congrArg (fun n : ℝ => n ^ s.layout.scale)
    (s.views_resolution_code (s.candidateIndex a) j)

/-- Geometry, the predeclared reference tests and the selected original
weighted score give one fully good raw stage, retaining the original
laws, priors and weights. -/
theorem exists_good_stage_of_selected_candidate
    (s : StagePath ctx source k R δ) (al : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ al.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent)
    (j : ℕ) (a : Fin s.layout.L)
    (node : ℝ → Fin (s.views (s.candidateIndex a)).count)
    (layers : Fin (s.views (s.candidateIndex a)).count →
      Layer (W (s.views (s.candidateIndex a)).parent
        ((s.views (s.candidateIndex a)).suffixChain.sample j)))
    {α ε : ℝ} {us : Finset ℝ}
    (hgeo : (s.candidateStage al pe base j a node layers α).GeometryGood ctx.dstar ctx.κ k R δ)
    (href : Reference.CandidateInput (s.candidateStage al pe base j a node layers α)
      ctx.dstar (min ctx.S₀ 1) R (s.graphK j) s.layout.m ε pe.τ pe.γ us)
    (hα : 0 < α) (hαtwo : 2 ≤ s.tangentN j ^ α) (hαδ : α ≤ δ)
    (hscore :
      (∑ g : Fin (W (s.views (s.candidateIndex a)).parent
          ((s.views (s.candidateIndex a)).suffixChain.sample j)),
        ω (s.views (s.candidateIndex a)).parent
          ((s.views (s.candidateIndex a)).suffixChain.sample j) g *
          Info.rlScore (s.worldLaw pe base j (s.candidateIndex a) g)
            (Info.canonX (s.tangentN j) s.layout.m
              (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m))
            (Info.canonY s.layout.m (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m))
            (Info.canonZ s.layout.m (Info.canonM (s.tangentN j) (s.graphK j) s.layout.m))) ≤
        ((∑ g, ENNReal.ofReal (ω (s.views (s.candidateIndex a)).parent
            ((s.views (s.candidateIndex a)).suffixChain.sample j) g) *
          s.worldLaw pe base j (s.candidateIndex a) g univ).toReal / 2) *
            Real.log (s.tangentN j ^ α)) :
    ∃ st : RawStage, st.Good ctx.dstar ctx.κ (min ctx.S₀ 1) k R δ := by
  let st := s.candidateStage al pe base j a node layers α
  have hN : st.N = s.tangentN j := s.candidateStage_resolution al pe base j a node layers α
  refine ⟨Reference.withReference st (s.graphK j) s.layout.m α,
    Reference.good_withReference st hgeo href s.layout.m_stage hα ?_ hαδ ?_⟩
  · rw [hN]
    exact hαtwo
  · change (∑ g : Fin st.W, st.p.weight st.sample g *
        Info.canonicalScore st.N (s.graphK j) s.layout.m (st.σ g)) ≤
      ((∑ g, ENNReal.ofReal (st.p.weight st.sample g) * st.σ g univ).toReal / 2) *
        Real.log (st.N ^ α)
    rw [hN]
    exact hscore

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
