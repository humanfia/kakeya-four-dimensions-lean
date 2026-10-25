/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/Defect.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.Model

/-! The common output grid is chosen before the depths. Reapply the universal
endpoint engine with this weaker defect exponent, so its palette bins already
use the required grid and retain their original palette numerators. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Filter

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

def withDefect (cfg : Data α) (E : ℝ) : Data α := { cfg with e₀ := E }

/-- Decreasing the positive horizontal defect exponent preserves every prepared
hypothesis; the original measures, assignments and palette are unchanged. -/
theorem Prepared.withDefect (h : cfg.Prepared) {E : ℝ} (hE : 0 < E)
    (hEe : E ≤ cfg.e₀) : (Data.withDefect cfg E).Prepared := by
  have hatlas : (Data.withDefect cfg E).Atlas := by
    intro R hR
    filter_upwards [h.atlas R hR] with k hk
    intro s hs hsU
    rcases hk s hs hsU with ⟨hTlo, hTup, hmeas, hdisj, hlabel, hcover, hcolor⟩
    refine ⟨hTlo, hTup, hmeas, hdisj, ?_, hcover, hcolor⟩
    intro i
    rcases hlabel i with ⟨hνlo, hνup, hμlo, hc, hF, hgeom, hfit, hnd, hhor⟩
    refine ⟨hνlo, hνup, hμlo, hc, hF, hgeom, hfit, hnd, ?_⟩
    intro hh
    rcases hhor hh with ⟨hP, hdef, hcenter, haffine⟩
    refine ⟨hP, ?_, hcenter, haffine⟩
    filter_upwards [hdef] with p hp
    exact hp.trans (Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ cfg.N k by linarith [h.scale k]) (neg_le_neg hEe))
  exact {
    scale := h.scale
    scale_limit := h.scale_limit
    subpower := h.subpower
    dimension_nonneg := h.dimension_nonneg
    dimension_lt_one := h.dimension_lt_one
    rate_pos := h.rate_pos
    rate_le_one := h.rate_le_one
    transverse_pos := h.transverse_pos
    palette_pos := h.palette_pos
    palette_le_one := h.palette_le_one
    depth_pos := h.depth_pos
    defect_pos := hE
    subcritical_rate := h.subcritical_rate
    horizontal_rate := h.horizontal_rate
    basic := h.basic
    caps := h.caps
    atlas := hatlas
    nested := h.nested
  }

end Data

/-- The endpoint arrays can be obtained directly at any smaller positive grid
exponent, without coarsening labels or changing palette numerators. -/
theorem endpoint_at_smaller_defect (hengine : EndpointEngine)
    {α : Type} [MeasurableSpace α] {cfg : Data α} (h : cfg.Prepared)
    {E : ℝ} (hE : 0 < E) (hEe : E ≤ cfg.e₀) : (Data.withDefect cfg E).Endpoint :=
  hengine α (Data.withDefect cfg E) (h.withDefect hE hEe)

end Submission.Obl.k4_subcritical_corrected_scalar_charts
