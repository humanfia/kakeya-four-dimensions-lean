-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.GradientFreeze, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/GradientFreeze.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/GradientFreeze.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/GradientFreeze.lean. Existing source attributions are preserved below.

-- Adapted from this LOT tree, o204, session x0747, commit7ddecf81.
-- Original file: Submission/Obl/k4_uniform_sampled_isotropic_branches/GradientFreeze.lean; existing source attributions retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SpacetimeGradient

/-! # Freeze actual derivatives using the second jet on the comparison ball -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

/-- The second iterated derivative and the derivative of the derivative
have exactly the same operator norm. -/
theorem norm_second_derivative (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (z : EuclideanSpace ℝ (Fin 3)) :
    ‖fderiv ℝ (fderiv ℝ f) z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := by
  simpa only [norm_iteratedFDeriv_one] using
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (n := 1) (x := z))

/-- The comparison-domain second-jet bound supplies the actual derivative
freeze error between any two used base points, by the mean value theorem. -/
theorem derivative_freeze_of_second_jet
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : IsOpen U) (hconvex : Convex ℝ U) (hf : ContDiffOn ℝ 2 f U)
    {M : ℝ} (hsecond : ∀ z ∈ U, ‖iteratedFDeriv ℝ 2 f z‖ ≤ M)
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U) (hy : y ∈ U) :
    ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ M * ‖y - x‖ := by
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hdf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
    (fun z hz => by rw [norm_second_derivative]; exact hsecond z hz) hconvex hx hy

/-- A fine base bin of radius `r` freezes the actual spatial gradient.
Both the directional tests and the strip cap are charged to the same
original law, so the result also applies to the residual `f - Q`. -/
theorem gradient_bound_from_second_jet_and_original_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V) (S : Set Ω)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (z : Ω → EuclideanSpace ℝ (Fin 3))
    (z₀ : EuclideanSpace ℝ (Fin 3)) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : IsOpen U) (hconvex : Convex ℝ U) (hf : ContDiffOn ℝ 2 f U)
    (hz₀ : z₀ ∈ U) (hz : ∀ ω ∈ S, z ω ∈ U) (W : Ω → ℝ)
    {δ K E M r B : ℝ} {threshold : ENNReal}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hE : 0 ≤ E) (hM : 0 ≤ M) (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hsecond : ∀ x ∈ U, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M)
    (hnear : ∀ ω ∈ S, ‖z ω - z₀‖ ≤ r)
    (hbreadth : ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
      μ (V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold)
    (hmass : threshold < μ S)
    (hspeed : ∀ ω ∈ S, ‖V ω‖ ≤ B)
    (hhidden : ∀ ω ∈ S, |W ω| ≤ K)
    (htest : ∀ ω ∈ S, |fderiv ℝ f (z ω) (spacetimeDirection (V ω)) - W ω| ≤ E) :
    let R := K + E + M * r + B * (2 * (M * r))
    ‖derivativeSpatialRow (fderiv ℝ f z₀)‖ ≤ R / δ ∧
      ‖fderiv ℝ f z₀‖ ≤ R + (B + 2) * (R / δ) := by
  apply derivative_bound_from_original_tests μ V hV S (fun ω => fderiv ℝ f (z ω))
    (fderiv ℝ f z₀) W hδ hK hE (show 0 ≤ M * r by positivity) hB
    hbreadth hmass hspeed hhidden htest
  intro ω hω
  exact (derivative_freeze_of_second_jet f U hU hconvex hf hsecond hz₀ (hz ω hω)).trans
    (mul_le_mul_of_nonneg_left (hnear ω hω) hM)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
