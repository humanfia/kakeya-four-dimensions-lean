/-
Adapted from this LOT tree, o118, session x0400, commit bd322ee595fd,
Submission/Obl/k4_extremal_profile_setup/VariableNativeDepth.lean.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.WorldMeasure
import Submission.Obl.k4_remainder_pure_profile_normalization.VaryingDepth
import Submission.Obl.k4_remainder_pure_profile_normalization.Profile

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open Set MeasureTheory Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open scoped ENNReal Topology

/-- The original pure-density exponent is stable under converging dyadic depth
adjustments, with all world weights and endpoint cases included. -/
theorem Data.Valid.sampledDensity_at_tendsto_depth {p : Data} (hp : p.Valid)
    {a : ℕ → ℝ} {r : ℝ} (hr : r ∈ Icc (0 : ℝ) p.L)
    (ha : Tendsto a atTop (𝓝 r)) (hamem : ∀ᶠ k in atTop, a k ∈ Icc (0 : ℝ) p.L) :
    HasTypicalDensity p.N p.sampleMeasure (fun k => p.sampledDensity (a k) k) (p.f r) := by
  have hf : ProfileIncrement p.f p.L := hp.2.2.2.2.2.2.2.2.2.2.2.1
  exact typicalDensity_on_Icc_at_tendsto_depth p.N
    (fun k => by linarith [hp.N_ge k]) hp.2.1 p.sampleMeasure p.sampledDensity p.f
    hp.L_pos.le hf.continuousOn
    (fun t ht => hp.sampledDensity_typical ht.1 ht.2)
    (fun t ht s hs hts k => hp.sampledDensity_antitone ht.1 hts hs.2 k) hr ha hamem

end Submission.Obl.k4_remainder_pure_profile_normalization
