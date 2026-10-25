-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.GeometricBootstrap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.PrismEndpoint
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedBootstrap

namespace WangZahlLot.Obl.wz_broad_grains_improvement

/-- The geometric part of the global gain is complete. The remaining
analytic premise is the all-scale Frostman volume theorem. -/
theorem uniform_gain_of_frostman {σ ω : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hFrostman : FrostmanAllScales) : UniformGain σ ω :=
  uniform_gain_of_aligned_one_scale hσ hσ2 hω hω1 hE hFrostman
    (aligned_one_scale_of_estimate hσ hσ2 hω hω1 hE)

/-- The all-scale Frostman volume theorem closes the exact frozen
improvement through its original-family gain branch. -/
theorem improvement_of_frostman {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1/2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hFrostman : FrostmanAllScales) (hε : 0 < ε) : L σ ω ζ ε :=
  improvement_of_uniform_gain hε (uniform_gain_of_frostman hσ hσ2 hω hω1 hE hFrostman)

end WangZahlLot.Obl.wz_broad_grains_improvement
