import Submission.Obl.k4_horizontal_endpoint_three_projections.Expanded
import Submission.Obl.k4_horizontal_endpoint_three_projections.PairedInterface
import Submission.Obl.k4_subcritical_endpoint_native_pairing
import Submission.Obl.k4_subcritical_corrected_scalar_charts
import Submission.Obl.k4_subcritical_chart_projection

namespace Submission.Obl.k4_horizontal_endpoint_three_projections

/-- Repackage the Mathlib-only frozen comparison statement. -/
theorem pairedComparison_from_child : Matching → PairedComparison := by
  intro h α inst cfg hp
  exact Submission.k4_subcritical_endpoint_native_pairing h cfg.N cfg.K cfg.d cfg.κ cfg.ℓ cfg.S cfg.U cfg.e₀ α
    cfg.ν cfg.μ cfg.ρ cfg.π cfg.b cfg.P cfg.T cfg.n cfg.j cfg.A cfg.B cfg.c cfg.F
    hp.scale hp.scale_limit hp.subpower hp.dimension_nonneg hp.dimension_lt_one
    hp.rate_pos hp.rate_le_one hp.transverse_pos hp.palette_pos hp.palette_le_one
    hp.depth_pos hp.defect_pos hp.subcritical_rate hp.horizontal_rate
    hp.basic hp.caps hp.atlas hp.nested

/-- Repackage the Mathlib-only frozen directional-chart statement. -/
theorem correctedCharts_from_child : CorrectedCharts := by
  intro α inst cfg hp
  exact Submission.k4_subcritical_corrected_scalar_charts cfg.N cfg.K cfg.d cfg.κ cfg.ℓ cfg.S cfg.U cfg.e₀ α
    cfg.ν cfg.μ cfg.ρ cfg.π cfg.b cfg.P cfg.T cfg.n cfg.j cfg.A cfg.B cfg.c cfg.F
    hp.scale hp.scale_limit hp.subpower hp.dimension_nonneg hp.dimension_lt_one
    hp.rate_pos hp.rate_le_one hp.transverse_pos hp.palette_pos hp.palette_le_one
    hp.depth_pos hp.defect_pos hp.subcritical_rate hp.horizontal_rate
    hp.basic hp.caps hp.atlas hp.nested

/-- Repackage the Mathlib-only frozen Scalar/physical-return statement. -/
theorem scalarReturn_from_child : Scalar → ScalarReturn := by
  intro h α inst cfg hp
  exact Submission.k4_subcritical_chart_projection h cfg.N cfg.K cfg.d cfg.κ cfg.ℓ cfg.S cfg.U cfg.e₀ α
    cfg.ν cfg.μ cfg.ρ cfg.π cfg.b cfg.P cfg.T cfg.n cfg.j cfg.A cfg.B cfg.c cfg.F
    hp.scale hp.scale_limit hp.subpower hp.dimension_nonneg hp.dimension_lt_one
    hp.rate_pos hp.rate_le_one hp.transverse_pos hp.palette_pos hp.palette_le_one
    hp.depth_pos hp.defect_pos hp.subcritical_rate hp.horizontal_rate
    hp.basic hp.caps hp.atlas hp.nested

end Submission.Obl.k4_horizontal_endpoint_three_projections
