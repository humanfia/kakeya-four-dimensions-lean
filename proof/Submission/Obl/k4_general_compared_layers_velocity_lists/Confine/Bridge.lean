-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Confine.Bridge; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Model
import Submission.Obl.k4_general_parent_projected_layers.Model

/-!
# The general parent as a prepared model of accepted o253

`Parent` (the frozen data of this obligation) and the `Parameters`/`PreparedModel`
pair of accepted o253 (`k4_general_parent_projected_layers/Model.lean`) carry the
same fields. The validity predicates agree up to unfolding the trajectory
(`Data.x` versus `K4ContactNormalization.point`), the dyadic blocks (`Data.I`
versus `PreparedModel.interval`) and the true block length.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α]

/-- The numerical parameters of a general parent. -/
def toParams (p : Parent α) : Parameters := ⟨p.N, p.K, p.d, p.κ, p.ℓ, p.S, p.U, p.e₀⟩

/-- The measures, trajectories and true labels of a general parent. -/
def toModel (p : Parent α) : PreparedModel α :=
  ⟨p.ν, p.μ, p.ρ, p.π, p.b, p.P, p.T, p.n, p.j, p.A, p.B, p.c, p.F⟩

theorem Valid.toParams_valid {p : Parent α} (h : p.Valid) : p.toParams.Valid :=
  ⟨h.scale, h.scale_limit, h.subpower, h.dimension_nonneg, h.dimension_lt_one, h.rate_pos,
    h.rate_le_one, h.transverse_pos, h.palette_pos, h.palette_le_one, h.depth_pos, h.defect_pos⟩

theorem Valid.toModel_common {p : Parent α} (h : p.Valid) : p.toModel.Common p.toParams :=
  h.basic

theorem Valid.toModel_caps {p : Parent α} (h : p.Valid) : p.toModel.Caps p.toParams :=
  h.caps

theorem AtDepth.toAtlasAt {p : Parent α} {k : ℕ} {s R : ℝ} (hat : p.AtDepth k s R) :
    p.toModel.AtlasAt p.toParams R k s :=
  hat

theorem Valid.eventually_atlasAt {p : Parent α} (h : p.Valid) {R : ℝ} (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ p.U → p.toModel.AtlasAt p.toParams R k s := by
  filter_upwards [h.prepared R hR] with k hk s hs hsU
  exact (hk s hs hsU).toAtlasAt

theorem toModel_x (p : Parent α) (k : ℕ) (l : α) (t : ℝ) :
    p.toModel.x k l t = p.x k l t :=
  rfl

theorem toModel_q (p : Parent α) (k : ℕ) (s : ℝ) :
    p.toModel.q k s = ((2 : ℝ) ^ p.T k s)⁻¹ := by
  simp only [PreparedModel.q, toModel, zpow_neg, zpow_natCast]

theorem toParams_width (p : Parent α) (k : ℕ) (s : ℝ) :
    PreparedModel.width p.toParams k s = p.N k ^ (-s) :=
  rfl

theorem toParams_narrow (p : Parent α) (k : ℕ) (s : ℝ) :
    PreparedModel.narrow p.toParams k s = p.N k ^ (-p.ℓ * s) :=
  rfl

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
