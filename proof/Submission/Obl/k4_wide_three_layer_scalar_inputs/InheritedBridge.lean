import Submission.Obl.k4_wide_three_layer_scalar_inputs.Model
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Model

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- Transfer the original data to the adapted comparison kernels without
changing any law, true assignment, chart or graph. -/
abbrev comparisonData : Inherited.Data α :=
  ⟨cfg.N, cfg.K, cfg.d, cfg.κ, cfg.ℓ, cfg.S, cfg.U, cfg.e₀,
    cfg.ν, cfg.μ, cfg.ρ, cfg.π, cfg.b, cfg.P, cfg.T, cfg.n,
    cfg.j, cfg.A, cfg.B, cfg.c, cfg.F⟩

theorem Valid.comparisonData {cfg : Data α} (h : cfg.Valid) :
    cfg.comparisonData.Valid := by
  exact ⟨h.scale, h.scale_limit, h.subpower.1, h.subpower.2,
    h.dimension_nonneg, h.dimension_lt_one, h.rate_pos, h.rate_le_one,
    h.transverse_pos, h.palette_pos, h.palette_le_one, h.depth_pos,
    h.defect_pos, h.horizontal_rate, h.basic, h.caps, h.atlas, h.nested⟩

end Data

end Submission.Obl.k4_wide_three_layer_scalar_inputs
