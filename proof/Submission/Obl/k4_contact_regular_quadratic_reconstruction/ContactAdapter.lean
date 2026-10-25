import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Model
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.Model

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open MeasureTheory Set Filter MvPolynomial

noncomputable section

namespace Model

variable {α : Type} [MeasurableSpace α] {cfg : Model α}

/-- The preparation context is supplied by exactly the frozen original model.
In particular it requires neither affine palettes nor a horizontal atlas. -/
theorem Valid.toContactProblem (h : cfg.Valid) : Transfer.ContactProblem cfg :=
  ⟨⟨h.scale, h.scale_limit, h.subpower, h.dimension_nonneg, h.dimension_lt_one,
      h.rate_pos, h.rate_le_one, h.transverse_pos, h.palette_pos, h.palette_le_one,
      h.depth_pos, h.defect_pos⟩,
    h.basic, h.caps, h.atlas, h.nested, h.contact, h.equal_rate⟩

/-- One positive horizon leaves the contact error smaller than the time zoom. -/
theorem Valid.exists_contact_horizon (h : cfg.Valid) :
    ∃ V : ℝ, 0 < V ∧ V ≤ cfg.U ∧ cfg.κ * V ≤ cfg.e₀ / 4 := by
  let V := min cfg.U (cfg.e₀ / (4 * cfg.κ))
  have hκ : 0 < cfg.κ := h.rate_pos
  have hV : 0 < V := lt_min h.depth_pos (div_pos h.defect_pos (by positivity))
  refine ⟨V, hV, min_le_left _ _, ?_⟩
  calc
    cfg.κ * V ≤ cfg.κ * (cfg.e₀ / (4 * cfg.κ)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hκ.le
    _ = cfg.e₀ / 4 := by field_simp [ne_of_gt hκ]

end Model

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
