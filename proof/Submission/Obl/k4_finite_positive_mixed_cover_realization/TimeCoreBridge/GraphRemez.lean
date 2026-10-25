-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/GraphRemez.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/GraphRemez.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Directional

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set Metric

/-- A positive-volume common-base fit gives a norm bound for the difference from the
true sheet on the full comparison half-ball. -/
theorem exists_sheet_difference_remez (h : algebraicRemez) (D : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ f g : RealSheet D,
      ∀ (E : Set Real3) (θ V : ℝ),
      MeasurableSet E → E ⊆ closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 ≤ V →
      ENNReal.ofReal θ * volume (closedBall (0 : Real3) (1 / 2)) ≤ volume E →
      (∀ x ∈ E, ‖f.f (emb x) - g.f (emb x)‖ ≤ V) →
      ∀ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 →
        ‖f.f (emb x) - g.f (emb x)‖ ≤ C * θ ^ (-C) * V := by
  obtain ⟨E, hE⟩ :=
    Submission.Obl.k4_algebraic_real_jet_comparison.exists_sheet_difference_degree 3 D
  obtain ⟨C, hC, hremez⟩ := h 3 E
  refine ⟨C, hC, ?_⟩
  intro f g S θ V hS hSsub hθ hθ1 hV hmass hbound x hx
  obtain ⟨P, hP, hdegree, heq⟩ := hE f.f g.f
    ⟨f.P, f.nonzero, f.degree, f.equation⟩ ⟨g.P, g.nonzero, g.degree, g.equation⟩
  apply hremez P (fun z => f.f z - g.f z) hP hdegree (f.holomorphic.sub g.holomorphic) heq
    (fun y hy => ?_) S θ V hS hSsub hθ hθ1 hV hmass hbound x hx
  simp only [Complex.sub_im]
  change (f.f (emb y)).im - (g.f (emb y)).im = 0
  rw [f.real_on_real y hy, g.real_on_real y hy, sub_self]

/-- The agreement set used for the matched projection is measurable from local holomorphy. -/
theorem measurableSet_sheet_agreement {D : ℕ} (f g : RealSheet D) (V : ℝ) :
    MeasurableSet {x : Real3 | ‖x‖ ≤ (1 : ℝ) / 2 ∧ ‖f.f (emb x) - g.f (emb x)‖ ≤ V} := by
  have hmaps : MapsTo emb (closedBall (0 : Real3) (1 / 2)) (ball 0 4) := by
    intro x hx
    rw [mem_ball_zero_iff, emb.norm_map]
    have hh := mem_closedBall_zero_iff.mp hx
    linarith
  have hf := f.holomorphic.continuousOn.comp emb.continuous.continuousOn hmaps
  have hg := g.holomorphic.continuousOn.comp emb.continuous.continuousOn hmaps
  simpa only [mem_closedBall_zero_iff, Pi.sub_apply, Function.comp_apply] using
    (isClosed_closedBall.isClosed_le (hf.sub hg).norm continuousOn_const).measurableSet

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
