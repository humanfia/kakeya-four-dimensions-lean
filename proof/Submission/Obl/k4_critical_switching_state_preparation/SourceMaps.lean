/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/SourceMaps.lean.
   Existing source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.SourceRegularity

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The exact midpoint intercept is measurable on the original incidence
space, before finite coding or probability normalization. -/
theorem measurable_midpointValue (h : cfg.Valid) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) : Measurable (cfg.midpointValue k s i L) := by
  have hb : Measurable (cfg.b k) := (h.basic k).1
  unfold midpointValue affineResidualIntercept affineResidualSlope
  fun_prop

/-- Both parts of the actual pair code are measurable on the same source. -/
theorem measurable_sourcePair (h : cfg.Valid) (k : ℕ) (s : ℝ)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (a δ : ℝ) :
    Measurable (cfg.sourcePair k s i L a δ) :=
  measurable_pairCode a δ (measurable_midpointValue h k s i L)
    (measurable_framedPoint h k s i)

end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
