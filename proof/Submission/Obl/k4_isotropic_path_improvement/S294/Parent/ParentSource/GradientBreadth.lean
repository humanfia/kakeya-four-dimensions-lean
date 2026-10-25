-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.GradientBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/GradientBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/GradientBreadth.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/GradientBreadth.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.RowComparison

/-!
# Directional tests bound a frozen gradient on a broad original law

A substantial collection of source trajectories tests one gradient row.
Its spatial part cannot be large because that would place every tested
velocity in a thin strip. The source measure is never normalized.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Bounded directional derivatives on a substantial original-law family
bound both parts of one frozen gradient, provided that same original law
has a planar strip cap. -/
theorem gradient_row_bound_from_directional_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V)
    (S : Set Ω) {δ R B a : ℝ} {b : EuclideanSpace ℝ (Fin 2)}
    {threshold : ENNReal} (hδ : 0 < δ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hbreadth : ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
      μ (V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold)
    (hmass : threshold < μ S)
    (hspeed : ∀ ω ∈ S, ‖V ω‖ ≤ B)
    (htest : ∀ ω ∈ S, |a + inner ℝ (V ω) b| ≤ R) :
    ‖b‖ ≤ R / δ ∧ |a| ≤ R + B * (R / δ) := by
  let Q : Set (EuclideanSpace ℝ (Fin 2)) := {v | |a + inner ℝ v b| ≤ R}
  have hQm : MeasurableSet Q := measurableSet_le (by fun_prop) measurable_const
  have hsub : S ⊆ V ⁻¹' Q := fun ω hω => htest ω hω
  have hmassQ : threshold < (μ.map V) Q := by
    rw [Measure.map_apply hV hQm]
    exact hmass.trans_le (measure_mono hsub)
  have hstrip : ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
      (μ.map V) (Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold := by
    intro n hn c
    rw [Measure.map_apply hV (Submission.Lib.K4VelocityStrips.measurableSet_affineStrip n c δ)]
    exact hbreadth n hn c
  have hrow := spatial_row_comparison_of_breadth (μ.map V) Q hδ
    (show 0 ≤ R / 2 by positivity) hstrip hmassQ
    (a := a) (a' := 0) (b := b) (b' := 0) (by
      intro v hv
      change |a + inner ℝ v b| ≤ R at hv
      simpa only [sub_zero, show 2 * (R / 2) = R by ring] using hv)
  have hb : ‖b‖ ≤ R / δ := by
    simpa only [sub_zero, show 2 * (R / 2) = R by ring] using hrow
  have hS : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h, measure_empty] at hmass
    exact (not_lt_of_ge bot_le) hmass
  obtain ⟨ω, hω⟩ := hS
  refine ⟨hb, ?_⟩
  calc
    |a| = |(a + inner ℝ (V ω) b) - inner ℝ (V ω) b| := by ring_nf
    _ ≤ |a + inner ℝ (V ω) b| + |inner ℝ (V ω) b| := abs_sub _ _
    _ ≤ R + ‖V ω‖ * ‖b‖ := add_le_add (htest ω hω) (abs_real_inner_le_norm _ _)
    _ ≤ _ := by gcongr; exact hspeed ω hω

/-- Freeze an actual varying gradient at a nearby point before applying
breadth. The freeze error is charged using the original speed bound. -/
theorem gradient_row_bound_from_nearby_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V)
    (S : Set Ω) (aa W : Ω → ℝ) (bb : Ω → EuclideanSpace ℝ (Fin 2))
    {δ K E eA eB B a : ℝ} {b : EuclideanSpace ℝ (Fin 2)}
    {threshold : ENNReal} (hδ : 0 < δ) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (heA : 0 ≤ eA) (heB : 0 ≤ eB) (hB : 0 ≤ B)
    (hbreadth : ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
      μ (V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold)
    (hmass : threshold < μ S)
    (hspeed : ∀ ω ∈ S, ‖V ω‖ ≤ B)
    (hhidden : ∀ ω ∈ S, |W ω| ≤ K)
    (htest : ∀ ω ∈ S, |aa ω + inner ℝ (V ω) (bb ω) - W ω| ≤ E)
    (hfreezeA : ∀ ω ∈ S, |aa ω - a| ≤ eA)
    (hfreezeB : ∀ ω ∈ S, ‖bb ω - b‖ ≤ eB) :
    ‖b‖ ≤ (K + E + eA + B * eB) / δ ∧
      |a| ≤ (K + E + eA + B * eB) + B * ((K + E + eA + B * eB) / δ) := by
  apply gradient_row_bound_from_directional_tests μ V hV S hδ (by positivity) hB
    hbreadth hmass hspeed
  intro ω hω
  have hspatial : |inner ℝ (V ω) (b - bb ω)| ≤ B * eB := by
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hspeed ω hω) (by simpa only [norm_sub_rev] using hfreezeB ω hω)
        (norm_nonneg _) hB)
  have htime : |a - aa ω| ≤ eA := by simpa only [abs_sub_comm] using hfreezeA ω hω
  have heq : a + inner ℝ (V ω) b =
      (aa ω + inner ℝ (V ω) (bb ω) - W ω) + W ω +
        (a - aa ω) + inner ℝ (V ω) (b - bb ω) := by
    rw [inner_sub_right]
    ring
  rw [heq]
  have h₁ := abs_add_le
    ((aa ω + inner ℝ (V ω) (bb ω) - W ω) + W ω + (a - aa ω))
    (inner ℝ (V ω) (b - bb ω))
  have h₂ := abs_add_le ((aa ω + inner ℝ (V ω) (bb ω) - W ω) + W ω) (a - aa ω)
  have h₃ := abs_add_le (aa ω + inner ℝ (V ω) (bb ω) - W ω) (W ω)
  linarith [htest ω hω, hhidden ω hω]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
