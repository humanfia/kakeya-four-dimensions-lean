-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.GlobalEndpoint.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.GeometricBootstrap
import Submission.WZ.Obl.wz_broad_grains_improvement.StrictBootstrap
import Submission.WZ.Obl.wz_broad_grains_improvement.Frostman.Assembly

namespace WangZahlLot.Obl.wz_broad_grains_improvement

/-- The geometric iteration and the all-scale Frostman theorem give a
uniform volume gain for every normalized admissible family. -/
theorem uniform_gain {σ ω : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) : UniformGain σ ω :=
  uniform_gain_of_frostman hσ hσ2 hω hω1 hE Frostman.Assembly.all_scales

/-- The original-family volume gain supplies the frozen improvement alternative. -/
theorem improvement {σ ω ζ ε : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) (hε : 0 < ε) : L σ ω ζ ε :=
  improvement_of_uniform_gain hε (uniform_gain hσ hσ2 hω hω1 hE)

/-- The same gain supplies the strict exponent improvement used upstream. -/
theorem normalized_strict_improvement {σ ω : ℝ}
    (hσ : 0 < σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hE : E σ ω) :
    ∃ g : ℝ, 0 < g ∧ g ≤ ω ∧ WangZahlLot.Obl.wz_endpoint_bootstrap.Estimate σ (ω - g) :=
  UniformGain.strict_improvement hω (uniform_gain hσ hσ2 hω hω1 hE)

end WangZahlLot.Obl.wz_broad_grains_improvement
