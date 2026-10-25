-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/RecenterSheets.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/RecenterSheets.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.LocalSheets

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set Metric

/-- Move a comparison sheet to a common nearby center, preserving its algebraic degree.
The margin also keeps all needed real points in the original real unit ball. -/
noncomputable def recenterRealSheet {D : ℕ} (F : RealSheet D) (a : Real3)
    (ha : ‖a‖ ≤ (1 : ℝ) / 2) : RealSheet D := by
  have hsub : ball (emb a) (1 / 2) ⊆ ball (0 : Complex3) 4 := by
    intro z hz
    rw [mem_ball_zero_iff]
    have hz' : ‖z - emb a‖ < (1 : ℝ) / 2 := by simpa only [mem_ball, dist_eq_norm] using hz
    have hnorm : ‖z‖ ≤ ‖z - emb a‖ + ‖emb a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (z - emb a) (emb a)
    rw [emb.norm_map] at hnorm
    linarith
  have hreal (x : Real3) (hx : ‖x - a‖ < (1 : ℝ) / 2) : (F.f (emb x)).im = 0 := by
    apply F.real_on_real
    have hnorm : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - a) a
    linarith
  exact localRealSheet a (1 / 2) (by norm_num) F.f F.P F.nonzero F.degree
    (F.holomorphic.mono hsub) (fun z hz => F.equation z (hsub hz)) hreal

theorem recenterRealSheet_apply {D : ℕ} (F : RealSheet D) (a : Real3)
    (ha : ‖a‖ ≤ (1 : ℝ) / 2) (x : Real3) :
    (recenterRealSheet F a ha).f (emb x) = F.f (emb (a + (1 / 16 : ℝ) • x)) := by
  change F.f (emb a + ((((1 / 2 : ℝ) / 8) : ℝ) : ℂ) • emb x) = _
  norm_num only [show ((1 / 2 : ℝ) / 8) = 1 / 16 by norm_num]
  rw [← Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding_line]

theorem recenter_real_point_norm_le {a x : Real3} (ha : ‖a‖ ≤ (1 : ℝ) / 2)
    (hx : ‖x‖ ≤ 1) : ‖a + (1 / 16 : ℝ) • x‖ ≤ 1 := by
  have hnorm := norm_add_le a ((1 / 16 : ℝ) • x)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)] at hnorm
  nlinarith

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
