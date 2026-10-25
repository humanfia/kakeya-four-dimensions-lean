-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.OriginalValueVariation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/OriginalValueVariation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/OriginalValueVariation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/OriginalValueVariation.lean.
-- Only the source value-norming declarations used here are retained; earlier provenance is preserved.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.OriginalJetNorming

/-!
An earlier original entry norms an algebraic value prediction directly.
This requires no local velocity breadth and no polynomial coefficient
bound, and can resolve its variation over a still deeper history box.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

/-- The measurable norming set is constructed from the actual original
entry values. Its original base cap and full-reference floor supply the
volume needed by the frozen value-jet clause. -/
theorem original_value_jets_from_entry
    {D J : ℕ} (hjets : DenseJetBound D J)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → Base)
    (g : Base → ℝ) (hg : HasRealExtension D g)
    {A β valueBound : ℝ} (hA : 2 ≤ A) (hβ : 0 < β) (hvalue : 0 ≤ valueBound)
    (hmass : ENNReal.ofReal (β / A) ≤ μ univ)
    (hcap : ∀ U : Set Base, MeasurableSet U → μ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U)
    (hsource : ∀ᵐ p ∂μ, Z p ∈ closedBall (0 : Base) 1 ∧ |g (Z p)| ≤ valueBound) :
    ∀ j : ℕ, j ≤ 6 → ∀ x ∈ closedBall (0 : Base) 2,
      ‖iteratedFDeriv ℝ j g x‖ ≤ A ^ J * valueBound := by
  let E : Set Base := closedBall (0 : Base) 1 ∩ (fun x => |g x|) ⁻¹' Iic valueBound
  have hcont : ContinuousOn g (closedBall (0 : Base) 1) :=
    hg.contDiffOn.continuousOn.mono (closedBall_subset_ball (by norm_num : (1 : ℝ) < 4))
  have hE : MeasurableSet E :=
    (hcont.abs.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic).measurableSet
  exact original_dense_jet_bound hjets μ Z E hE inter_subset_left hA hβ hvalue hmass hcap
    hsource g hg (fun x hx => hx.2)

/-- Values of an algebraic prediction on an EARLIER original entry bound
its whole-core variation. No palette breadth, potential derivative or
input-format coefficient envelope is assumed. -/
theorem original_value_prediction_variation
    {D J : ℕ} (hjets : DenseJetBound D J)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → Base)
    (g : Base → ℝ) (hg : HasRealExtension D g)
    {A β valueBound : ℝ} (hA : 2 ≤ A) (hβ : 0 < β) (hvalue : 0 ≤ valueBound)
    (hmass : ENNReal.ofReal (β / A) ≤ μ univ)
    (hcap : ∀ U : Set Base, MeasurableSet U → μ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U)
    (hsource : ∀ᵐ p ∂μ, Z p ∈ closedBall (0 : Base) 1 ∧ |g (Z p)| ≤ valueBound)
    {x y : Base} (hx : x ∈ closedBall (0 : Base) 2) (hy : y ∈ closedBall (0 : Base) 2) :
    |g y - g x| ≤ (A ^ J * valueBound) * ‖y - x‖ := by
  have hgrad (z : Base) (hz : z ∈ closedBall (0 : Base) 2) :
      ‖fderiv ℝ g z‖ ≤ A ^ J * valueBound := by
    simpa only [norm_iteratedFDeriv_one] using
      original_value_jets_from_entry hjets μ Z g hg hA hβ hvalue hmass hcap hsource
        1 (by norm_num) z hz
  have hdiff (z : Base) (hz : z ∈ closedBall (0 : Base) 2) : DifferentiableAt ℝ g z := by
    have hz4 : z ∈ ball (0 : Base) 4 :=
      closedBall_subset_ball (by norm_num : (2 : ℝ) < 4) hz
    exact (hg.contDiffOn.contDiffAt (isOpen_ball.mem_nhds hz4)).differentiableAt (by simp)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hgrad (convex_closedBall (0 : Base) 2) hx hy

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
