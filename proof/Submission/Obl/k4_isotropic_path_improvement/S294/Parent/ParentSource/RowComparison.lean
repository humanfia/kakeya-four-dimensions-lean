-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.RowComparison, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/RowComparison.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/RowComparison.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/RowComparison.lean.
-- Existing source attributions are preserved below.

import Submission.Lib.K4VelocityStrips.StripIntersections

/-!
# Comparing two velocity rows on the same broad original law

Common directional tests force two rows to agree unless their common test set
fits a thin velocity strip. The mass comparison always uses the SAME preceding
law as the breadth assumption; sparse selections do not inherit breadth here.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal

/-- Subtracting two tests of the same hidden velocity yields a strip test. -/
theorem common_velocity_tests_difference
    {a a' W ε : ℝ} {b b' v : EuclideanSpace ℝ (Fin 2)}
    (h : |a + inner ℝ v b - W| ≤ ε)
    (h' : |a' + inner ℝ v b' - W| ≤ ε) :
    |(a - a') + inner ℝ v (b - b')| ≤ 2 * ε := by
  have heq : (a - a') + inner ℝ v (b - b') =
      (a + inner ℝ v b - W) - (a' + inner ℝ v b' - W) := by
    rw [inner_sub_right]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

/-- The spatial parts of two rows fitting a common substantial family are
close. A failure would put that entire family in one forbidden strip. -/
theorem spatial_row_comparison_of_breadth
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (Q : Set (EuclideanSpace ℝ (Fin 2)))
    {δ ε a a' : ℝ} {b b' : EuclideanSpace ℝ (Fin 2)} {threshold : ENNReal}
    (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hbreadth : ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
      μ (Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold)
    (hmass : threshold < μ Q)
    (htests : ∀ v ∈ Q, |(a - a') + inner ℝ v (b - b')| ≤ 2 * ε) :
    ‖b - b'‖ ≤ 2 * ε / δ := by
  by_contra h
  have hlarge : 2 * ε / δ < ‖b - b'‖ := lt_of_not_ge h
  have hn : 0 < ‖b - b'‖ := (div_nonneg (by positivity) hδ.le).trans_lt hlarge
  let n : EuclideanSpace ℝ (Fin 2) := ‖b - b'‖⁻¹ • (b - b')
  let c : ℝ := -(a - a') / ‖b - b'‖
  have hunit : ‖n‖ = 1 := by
    change ‖‖b - b'‖⁻¹ • (b - b')‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hsub : Q ⊆ Submission.Lib.K4VelocityStrips.affineStrip n c δ := by
    intro v hv
    change |inner ℝ v n - c| ≤ δ
    have heq : inner ℝ v n - c = ((a - a') + inner ℝ v (b - b')) / ‖b - b'‖ := by
      simp only [n, c, inner_smul_right, div_eq_mul_inv]
      ring
    rw [heq, abs_div, abs_of_pos hn]
    apply (div_le_iff₀ hn).mpr
    have hεgap := (div_lt_iff₀ hδ).mp hlarge
    exact (htests v hv).trans (by nlinarith)
  exact (not_le_of_gt hmass) ((measure_mono hsub).trans (hbreadth n hunit c))

/-- Two rows fitting the same hidden velocities are quantitatively close in
both their spatial and time components. -/
theorem row_comparison_of_common_velocity_tests
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (Q : Set (EuclideanSpace ℝ (Fin 2)))
    (W : EuclideanSpace ℝ (Fin 2) → ℝ)
    {δ ε K a a' : ℝ} {b b' : EuclideanSpace ℝ (Fin 2)} {threshold : ENNReal}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hbreadth : ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
      μ (Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold)
    (hmass : threshold < μ Q)
    (hspeed : ∀ v ∈ Q, ‖v‖ ≤ K)
    (hrow : ∀ v ∈ Q, |a + inner ℝ v b - W v| ≤ ε)
    (hrow' : ∀ v ∈ Q, |a' + inner ℝ v b' - W v| ≤ ε) :
    ‖b - b'‖ ≤ 2 * ε / δ ∧ |a - a'| ≤ 2 * ε + K * (2 * ε / δ) := by
  have htests : ∀ v ∈ Q, |(a - a') + inner ℝ v (b - b')| ≤ 2 * ε :=
    fun v hv => common_velocity_tests_difference (hrow v hv) (hrow' v hv)
  have hb := spatial_row_comparison_of_breadth μ Q hδ hε hbreadth hmass htests
  have hQne : Q.Nonempty := by
    by_contra h
    have hzero : μ Q = 0 := by rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty]
    rw [hzero] at hmass
    exact (not_lt_of_ge zero_le) hmass
  obtain ⟨v, hv⟩ := hQne
  refine ⟨hb, ?_⟩
  have hinner : |inner ℝ v (b - b')| ≤ K * (2 * ε / δ) :=
    (abs_real_inner_le_norm v (b - b')).trans
      (mul_le_mul (hspeed v hv) hb (norm_nonneg _) hK)
  have hsum := htests v hv
  have htriangle := abs_sub ((a - a') + inner ℝ v (b - b')) (inner ℝ v (b - b'))
  simp only [add_sub_cancel_right] at htriangle
  linarith

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
