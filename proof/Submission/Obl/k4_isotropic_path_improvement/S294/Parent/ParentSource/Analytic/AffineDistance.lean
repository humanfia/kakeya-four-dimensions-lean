-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.AffineDistance, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/AffineDistance.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/AffineDistance.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/AffineDistance.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/AffineDistance.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.AffineTransport

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

/-- The affine-distance scale has the lower witnesses required by local
restoration, together with arbitrarily close upper approximations. This
includes scale zero and does not require choosing a best affine approximant. -/
theorem exists_affine_distance_scale (f : Base → ℝ)
    (hf : ContinuousOn f (Metric.closedBall (0 : Base) 1)) :
    ∃ s : ℝ, 0 ≤ s ∧
      (∀ (c : ℝ) (L : Base →L[ℝ] ℝ), ∃ u ∈ Metric.closedBall (0 : Base) 1,
        s ≤ |f u - c - L u|) ∧
      (∀ ε : ℝ, s < ε → ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
        ∀ u ∈ Metric.closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) := by
  let U : Set Base := Metric.closedBall 0 1
  have hU : IsCompact U := isCompact_closedBall _ _
  have hUne : U.Nonempty := ⟨0, by simp [U]⟩
  let E : Set ℝ := {ε | 0 ≤ ε ∧ ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
    ∀ u ∈ U, |f u - c - L u| ≤ ε}
  have hEne : E.Nonempty := by
    obtain ⟨u, hu, hmax⟩ := hU.exists_isMaxOn hUne hf.abs
    refine ⟨|f u|, abs_nonneg _, 0, 0, ?_⟩
    simpa using (isMaxOn_iff.mp hmax)
  have hEbelow : BddBelow E := ⟨0, fun _ hε => hε.1⟩
  refine ⟨sInf E, le_csInf hEne (fun _ hε => hε.1), ?_, ?_⟩
  · intro c L
    have herr : ContinuousOn (fun u : Base => |f u - c - L u|) U :=
      ((hf.sub continuousOn_const).sub L.continuous.continuousOn).abs
    obtain ⟨u, hu, hmax⟩ := hU.exists_isMaxOn hUne herr
    have hmaxE : |f u - c - L u| ∈ E := ⟨abs_nonneg _, c, L, hmax⟩
    exact ⟨u, hu, csInf_le hEbelow hmaxE⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := exists_lt_of_csInf_lt hEne hε
    obtain ⟨_, c, L, hbound⟩ := hδ
    exact ⟨c, L, fun u hu => (hbound u hu).trans hδε.le⟩

/-- Any quantity controlled uniformly by every affine approximation error is
controlled by the affine-distance scale itself, including at scale zero. -/
theorem bound_by_affine_distance_scale (f : Base → ℝ) (s A X : ℝ)
    (hs : 0 ≤ s) (hA : 0 ≤ A)
    (happrox : ∀ ε : ℝ, s < ε → ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∀ u ∈ Metric.closedBall (0 : Base) 1, |f u - c - L u| ≤ ε)
    (hbound : ∀ (c : ℝ) (L : Base →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      (∀ u ∈ Metric.closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) → X ≤ A * ε) :
    X ≤ A * s := by
  by_cases hA0 : A = 0
  · obtain ⟨c, L, hcL⟩ := happrox (s + 1) (by linarith)
    simpa [hA0] using hbound c L (s + 1) (by linarith) hcL
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hε : s < s + δ / A := lt_add_of_pos_right _ (div_pos hδ hApos)
  obtain ⟨c, L, hcL⟩ := happrox (s + δ / A) hε
  have h := hbound c L (s + δ / A) (hs.trans_lt hε) hcL
  have heq : A * (s + δ / A) = A * s + δ := by field_simp
  simpa only [heq] using h

/-- The preceding construction supplies exactly the relative higher-derivative
bound and the affine-distance lower witnesses used in LocalBranchData. -/
theorem exists_affine_distance_scale_with_derivatives (f : Base → ℝ)
    (hf : ContinuousOn f (Metric.closedBall (0 : Base) 1))
    {A : ℝ} (hA : 0 ≤ A)
    (hrelative : ∀ (c : ℝ) (L : Base →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      (∀ u ∈ Metric.closedBall (0 : Base) 1, |f u - c - L u| ≤ ε) →
      ∀ j : ℕ, 2 ≤ j → j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : Base) 2,
        ‖iteratedFDeriv ℝ j f u‖ ≤ A * ε) :
    ∃ s : ℝ, 0 ≤ s ∧
      (∀ (c : ℝ) (L : Base →L[ℝ] ℝ), ∃ u ∈ Metric.closedBall (0 : Base) 1,
        s ≤ |f u - c - L u|) ∧
      (∀ j : ℕ, 2 ≤ j → j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : Base) 2,
        ‖iteratedFDeriv ℝ j f u‖ ≤ A * s) := by
  obtain ⟨s, hs, hlower, happrox⟩ := exists_affine_distance_scale f hf
  refine ⟨s, hs, hlower, ?_⟩
  intro j hj2 hj6 u hu
  apply bound_by_affine_distance_scale f s A _ hs hA happrox
  intro c L ε hε he
  exact hrelative c L ε hε he j hj2 hj6 u hu

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
