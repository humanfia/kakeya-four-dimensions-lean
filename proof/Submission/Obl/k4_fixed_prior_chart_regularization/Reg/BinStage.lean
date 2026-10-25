import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.Stages
import Submission.Lib.K4CoefficientBinRegularization.BinStage

namespace Submission.Obl.k4_fixed_prior_chart_regularization.Reg

/-- Use the accepted coefficient-bin regularization under the unchanged prior.
The two raw-chart structures have exactly the same fields. -/
theorem stageBin : StageBin := by
  intro d hd hd1 c hc ε hε
  obtain ⟨η, hη, hηε, N₀, hN₀, hbin⟩ :=
    Submission.Lib.K4CoefficientBinRegularization.Reg.stageBin d hd hd1 c hc ε hε
  refine ⟨η, hη, hηε, N₀, hN₀, ?_⟩
  intro N hN Ω mΩ ν hν y β γ E F hU hL hR hS
  have hinput : Submission.Lib.K4CoefficientBinRegularization.UnregularizedChart
      ν y β γ E F d (N ^ η) (N ^ (-c)) :=
    ⟨hU.measurable_y, hU.measurable_β, hU.measurable_γ, hU.measurable_F,
      hU.measurableSet_E, hU.subset_E, hU.bound_y, hU.bound_β, hU.bound_γ,
      hU.bound_F, hU.mass, hU.mixedCap, hU.support⟩
  obtain ⟨E', hsub, hU', hB⟩ := hbin N hN Ω ν hν y β γ E F hinput hL hR hS
  refine ⟨E', hsub, ?_, hB⟩
  exact ⟨hU'.measurable_y, hU'.measurable_β, hU'.measurable_γ, hU'.measurable_F,
    hU'.measurableSet_E, hU'.subset_E, hU'.bound_y, hU'.bound_β, hU'.bound_γ,
    hU'.bound_F, hU'.mass, hU'.mixedCap, hU'.support⟩

end Submission.Obl.k4_fixed_prior_chart_regularization.Reg
