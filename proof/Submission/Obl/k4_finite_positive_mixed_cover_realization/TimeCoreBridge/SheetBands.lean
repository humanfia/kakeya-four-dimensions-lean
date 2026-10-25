-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SheetBands.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/SheetBands.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.GraphRemez

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set Metric

/-- Real sheet fits to one hidden coordinate give a complex norm comparison. -/
theorem sheet_gap_of_real_fits {D : ℕ} (f g : RealSheet D) (x : Real3)
    (hx : ‖x‖ ≤ 1) (w : ℝ) {ηf ηg : ℝ}
    (hf : |w - (f.f (emb x)).re| ≤ ηf) (hg : |w - (g.f (emb x)).re| ≤ ηg) :
    ‖f.f (emb x) - g.f (emb x)‖ ≤ ηf + ηg := by
  have hfC : f.f (emb x) = ((f.f (emb x)).re : ℂ) := by
    apply Complex.ext <;> simp [f.real_on_real x hx]
  have hgC : g.f (emb x) = ((g.f (emb x)).re : ℂ) := by
    apply Complex.ext <;> simp [g.real_on_real x hx]
  rw [hfC, hgC, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |(f.f (emb x)).re - w| + |w - (g.f (emb x)).re| := abs_sub_le _ _ _
    _ ≤ _ := by rw [abs_sub_comm (f.f (emb x)).re w]; exact add_le_add hf hg

/-- Projection Remez gives the common-graph band on the real unit ball used by
local graph matching. The coefficient-independent norm comparison supplies the margin. -/
theorem exists_sheet_difference_band (h : algebraicRemez) (D : ℕ) :
    ∃ K C : ℝ, 1 ≤ K ∧ 1 ≤ C ∧ ∀ f g : RealSheet D,
      ∀ (E : Set Real3) (θ V : ℝ),
      MeasurableSet E → E ⊆ closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 < V →
      ENNReal.ofReal θ * volume (closedBall (0 : Real3) (1 / 2)) ≤ volume E →
      (∀ x ∈ E, ‖f.f (emb x) - g.f (emb x)‖ ≤ V) →
      ∀ x : Real3, ‖x‖ ≤ 1 → ‖f.f (emb x) - g.f (emb x)‖ ≤ K * (C * θ ^ (-C) * V) := by
  obtain ⟨C, hC, hremez⟩ := exists_sheet_difference_remez h D
  obtain ⟨degree, hdifference⟩ :=
    Submission.Obl.k4_algebraic_real_jet_comparison.exists_sheet_difference_degree 3 D
  obtain ⟨K, hK, hnorm⟩ :=
    Submission.Obl.k4_algebraic_real_jet_comparison.exists_sheet_norm_constant 3 degree
  refine ⟨K, C, hK, hC, ?_⟩
  intro f g E θ V hE hsub hθ hθ1 hV hmass hfit x hx
  have hrel := hdifference f.f g.f ⟨f.P, f.nonzero, f.degree, f.equation⟩
    ⟨g.P, g.nonzero, g.degree, g.equation⟩
  have hhalf := hremez f g E θ V hE hsub hθ hθ1 hV.le hmass hfit
  have hCpos : 0 < C := by linarith
  exact hnorm (fun z => f.f z - g.f z) hrel (f.holomorphic.sub g.holomorphic)
    (C * θ ^ (-C) * V) (by positivity) hhalf (emb x) (by simpa only [emb.norm_map] using hx)

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
