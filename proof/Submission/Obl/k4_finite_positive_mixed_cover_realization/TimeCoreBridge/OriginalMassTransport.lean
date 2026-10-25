-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/OriginalMassTransport.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
open MeasureTheory

/-- Original world weights commute with restriction and the observed cap. -/
theorem weighted_restrict_map_cap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (rho : Measure Y) (cov : Set X) (f : X → Y)
    (hf : Measurable f) {w H : ℝ} (hw : 0 ≤ w)
    (hcap : (mu.restrict cov).map f ≤ ENNReal.ofReal H • rho) :
    ((ENNReal.ofReal w • mu).restrict cov).map f ≤ ENNReal.ofReal (w * H) • rho := by
  rw [Measure.restrict_smul, Measure.map_smul _ hf.aemeasurable]
  apply Measure.le_iff.mpr
  intro Z hZ
  have hh := mul_le_mul' (le_rfl : ENNReal.ofReal w ≤ ENNReal.ofReal w)
    ((Measure.le_iff.mp hcap) Z hZ)
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_mul hw, mul_assoc] using hh


/-- A lower mass-to-cap ratio gives the same floor in the original weighted law. -/
theorem weighted_mass_floor_of_ratio {w H prior power geom theta : ℝ}
    {scale mass : ENNReal} (hw : 0 < w) (hH : 0 < H) (hp : 0 ≤ prior)
    (hscale : ENNReal.ofReal prior = scale)
    (hratio : theta ≤ ((w * prior) * power / geom) / (w * H))
    (hmass : scale * ENNReal.ofReal (power / geom) ≤ mass) :
    ENNReal.ofReal ((w * H) * theta) ≤ ENNReal.ofReal w * mass := by
  have htheta := (le_div_iff₀ (mul_pos hw hH)).mp hratio
  calc
    _ ≤ ENNReal.ofReal (w * (prior * power / geom)) := by
      apply ENNReal.ofReal_le_ofReal
      convert htheta using 1 <;> ring
    _ = ENNReal.ofReal w * (scale * ENNReal.ofReal (power / geom)) := by
      rw [ENNReal.ofReal_mul hw.le,
        show prior * power / geom = prior * (power / geom) by ring,
        ENNReal.ofReal_mul hp, hscale]
    _ ≤ _ := mul_le_mul' le_rfl hmass

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
