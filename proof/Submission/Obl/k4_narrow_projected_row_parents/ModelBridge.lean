/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/ModelBridge.lean.
   Earlier provenance comments in the source are retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.Model

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter

namespace Model

variable {α : Type} [MeasurableSpace α]

def parameters (cfg : Model α) : Submission.Obl.k4_general_parent_projected_layers.Parameters :=
  ⟨cfg.N, cfg.K, cfg.d, cfg.κ, cfg.ℓ, cfg.S, cfg.U, cfg.e₀⟩

def prepared (cfg : Model α) : Submission.Obl.k4_general_parent_projected_layers.PreparedModel α :=
  ⟨cfg.ν, cfg.μ, cfg.ρ, cfg.π, cfg.b, cfg.P, cfg.T, cfg.n, cfg.j,
    cfg.A, cfg.B, cfg.c, cfg.F⟩

theorem parameters_valid {cfg : Model α} (h : Valid cfg) : (parameters cfg).Valid :=
  ⟨h.scale, h.scale_limit, h.subpower, h.dimension_nonneg, h.dimension_lt_one,
    h.rate_pos, h.rate_le_one, h.transverse_pos, h.palette_pos, h.palette_le_one,
    h.depth_pos, h.defect_pos⟩

theorem prepared_valid {cfg : Model α} (h : Valid cfg) :
    (prepared cfg).Valid (parameters cfg) := by
  refine ⟨h.basic, h.caps, ?_, h.nested⟩
  intro R hR
  filter_upwards [h.atlas R hR] with k hk
  intro s hs hsU
  have hi := hk s hs hsU
  simpa [Submission.Obl.k4_general_parent_projected_layers.PreparedModel.AtlasAt,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.block, Submission.Obl.k4_general_parent_projected_layers.PreparedModel.interval,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.q, Submission.Obl.k4_general_parent_projected_layers.PreparedModel.width,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.narrow, Submission.Obl.k4_general_parent_projected_layers.PreparedModel.x,
    Submission.Obl.k4_general_parent_projected_layers.PreparedModel.fit, Submission.Lib.K4ContactNormalization.point,
    Submission.Obl.k4_critical_intercept_concentration.Data.x,
    Submission.Obl.k4_critical_intercept_concentration.Data.I,
    Submission.Obl.k4_critical_intercept_concentration.Data.fit,
    parameters, prepared] using hi

end Model

end Submission.Obl.k4_narrow_projected_row_parents
