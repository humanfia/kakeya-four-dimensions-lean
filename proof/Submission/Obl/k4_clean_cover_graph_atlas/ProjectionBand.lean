-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/ProjectionBand.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.ProjectionMass
import Submission.Obl.k4_clean_cover_graph_atlas.SheetBands

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Metric

/-- A surviving entry's original mass floor and base density ceiling put its sheet in
one common band around the true sheet. The measurable agreement set replaces the projection. -/
theorem exists_original_mass_sheet_band (h : algebraicRemez) (D : ℕ) :
    ∃ K C : ℝ, 1 ≤ K ∧ 1 ≤ C ∧ ∀ f g : RealSheet D,
      ∀ (μ : Measure Real3) (H m θ V : ℝ),
      0 < H → 0 < θ → θ ≤ 1 → 0 < V →
      μ ≤ ENNReal.ofReal H • volume →
      μ {x | ¬(‖x‖ ≤ (1 : ℝ) / 2 ∧ ‖f.f (emb x) - g.f (emb x)‖ ≤ V)} = 0 →
      ENNReal.ofReal m ≤ μ univ →
      ENNReal.ofReal θ * volume (closedBall (0 : Real3) (1 / 2)) ≤ ENNReal.ofReal (m / H) →
      ∀ x : Real3, ‖x‖ ≤ 1 → ‖f.f (emb x) - g.f (emb x)‖ ≤ K * (C * θ ^ (-C) * V) := by
  obtain ⟨K, C, hK, hC, hband⟩ := exists_sheet_difference_band h D
  refine ⟨K, C, hK, hC, ?_⟩
  intro f g μ H m θ V hH hθ hθ1 hV hcap hsupport hmass hθmass
  let E : Set Real3 := {x | ‖x‖ ≤ (1 : ℝ) / 2 ∧ ‖f.f (emb x) - g.f (emb x)‖ ≤ V}
  have hE : MeasurableSet E := measurableSet_sheet_agreement f g V
  have hEsub : E ⊆ closedBall 0 (1 / 2) := fun x hx => mem_closedBall_zero_iff.mpr hx.1
  have hEmass : ENNReal.ofReal (m / H) ≤ volume E :=
    projection_volume_floor μ volume E hE hH hcap hsupport hmass
  exact hband f g E θ V hE hEsub hθ hθ1 hV (hθmass.trans hEmass) (fun _ hx => hx.2)

end Submission.Obl.k4_clean_cover_graph_atlas
