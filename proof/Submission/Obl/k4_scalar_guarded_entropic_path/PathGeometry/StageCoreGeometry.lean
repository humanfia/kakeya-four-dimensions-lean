import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageCoreBudgets
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageCoreLayers
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StageNodes
import Submission.Obl.k4_scalar_guarded_entropic_path.ViewStageGeometry

/-! Every original candidate is a complete geometric raw stage on one
late common core. Reference coding and entropy selection can follow it. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx} {k : ℕ} {R δ : ℝ}

theorem eventually_candidate_geometry (s : StagePath ctx source k R δ) (hR : 1 < R)
    (hη : 0 < ctx.η) (allow : StageAllowances s)
    (pe : PreparationExponents s.layout.scale δ allow.v ctx.S₀ ctx.η)
    (base : (a : s.ViewIndex) → DensityTests (s.views a).parent)
    (htolerance : ∀ a, (base a).tolerance = pe.τ) :
    ∀ᶠ j in atTop, ∀ a : Fin s.layout.L,
      ∃ node : ℝ → Fin (s.views (s.candidateIndex a)).count,
      ∃ layers : Fin (s.views (s.candidateIndex a)).count →
          Layer (W (s.views (s.candidateIndex a)).parent
            ((s.views (s.candidateIndex a)).suffixChain.sample j)),
      ∀ (Mb : ℤ) (α : ℝ), RawStage.GeometryGood
        ((s.views (s.candidateIndex a)).toRawStage j s.layout.scale
          (Code.N (s.views (s.candidateIndex a)).parent
            ((s.views (s.candidateIndex a)).suffixChain.sample j) ^ allow.v)
          (δ / 1000)
          (Code.N (s.views (s.candidateIndex a)).parent
            ((s.views (s.candidateIndex a)).suffixChain.sample j) ^ (s.layout.scale * δ))
          allow.M₀ pe.ε (s.coreSet pe base j) node layers s.layout.m Mb α)
        ctx.dstar ctx.κ k R δ := by
  have hscale := s.layout.scale_pos
  have hδ : 0 < δ := hscale.trans_le s.layout.scale_error
  filter_upwards [s.eventually_power_envelopes hη allow pe base,
    s.eventually_original_layer_payloads hη allow pe base htolerance, allow.guard]
    with j henv hlayers hguard a
  let a₀ := s.candidateIndex a
  obtain ⟨node, hnode⟩ := s.exists_candidate_node hR a
  obtain ⟨layers, hgood⟩ := hlayers a₀ (Nat.succ_pos a.val)
  refine ⟨node, layers, ?_⟩
  intro Mb α
  have hres := s.views_resolution_code a₀ j
  have hlength : s.layout.scale * R < L (s.views a₀).parent := by
    have hLp : (1 / 2 : ℝ) < L (s.views a₀).parent := s.view_length a₀.val
    have hm : (0 : ℝ) ≤ s.layout.m := Nat.cast_nonneg _
    nlinarith only [s.layout.range_small, hLp, hscale, hm]
  apply (s.views a₀).toRawStage_geometry_good s.final_exact j k allow.M₀ s.layout.m Mb
    (s.coreSet pe base j) node layers hR hscale s.layout.scale_one s.layout.scale_error
    (by positivity : 0 < δ / 1000) (by linarith : δ / 1000 ≤ δ) allow.M_one
    (allow.formats a₀).2.1 (allow.formats a₀).2.2.1 (allow.formats a₀).2.2.2 hlength
  · rw [hres]
    exact henv a₀
  · rw [hres]
    exact hgood
  · exact hnode
  · intro r h hr hrL hh
    have hh' : h ≤ ctx.κ * r - s.layout.scale * δ / 1000 := by
      simpa only [mul_div_assoc] using hh
    rw [hres]
    exact hguard a₀ r h hr hrL hh'

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.StagePath
