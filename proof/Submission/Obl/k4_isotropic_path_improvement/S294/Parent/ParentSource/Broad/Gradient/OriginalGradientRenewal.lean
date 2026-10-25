-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.OriginalGradientRenewal, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/OriginalGradientRenewal.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/OriginalGradientRenewal.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/OriginalGradientRenewal.lean. Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/OriginalGradientRenewal.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.GradientRenewal
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.RelativeGradientJets

/-! # Whole-core residual renewal from actual original-law broad tests -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric

noncomputable section

/-- The original unnormalized entry floor and base cap give the real
volume used by value-jet norming. This involves no selected-group mass. -/
theorem original_entry_base_volume_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → EuclideanSpace ℝ (Fin 3))
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E)
    {A β : ℝ} (hA : 0 < A) (hβ : 0 < β)
    (hmass : ENNReal.ofReal (β / A) ≤ μ univ)
    (hcap : ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U →
      μ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U)
    (hsupp : ∀ᵐ ω ∂μ, Z ω ∈ E) : ENNReal.ofReal A⁻¹ ≤ volume E := by
  have hsource : μ (Z ⁻¹' E) = μ univ := by
    apply measure_congr
    filter_upwards [hsupp] with ω hω
    exact propext (iff_true_intro hω)
  apply (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.mpr hβ).ne' ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal A⁻¹ * ENNReal.ofReal β = ENNReal.ofReal (β / A) := by
      rw [mul_comm, ← ENNReal.ofReal_mul hβ.le, div_eq_mul_inv]
    _ ≤ μ univ := hmass
    _ = μ (Z ⁻¹' E) := hsource.symm
    _ ≤ ENNReal.ofReal β * volume E := hcap E hE
    _ = volume E * ENNReal.ofReal β := mul_comm _ _

/-- The frozen value-jet clause, the EARLIER original mass/base cap and
actual same-law broad cell tests give a gradient bound and oscillation on
the WHOLE core. The coordinate norming and relative Hessian estimates are
derived here; neither is a supplied geometric conclusion. -/
theorem original_entry_gradient_renewal
    {D J : ℕ} (hjets : ValueJetBound D J)
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ₀ : Measure Ω) (μ : ι → Measure Ω)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V)
    (S : ι → Set Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : ContDiffOn ℝ 2 g (ball 0 4))
    (hgext : ∀ j : Fin 3, exf D (gradientComponent g j))
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E)
    (hEball : E ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {A β ε r δ B : ℝ} (hA : 2 ≤ A) (hβ : 0 < β) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hmass₀ : ENNReal.ofReal (β / A) ≤ μ₀ univ)
    (hcap : ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U →
      μ₀ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U)
    (hsupp : ∀ᵐ ω ∂μ₀, Z ω ∈ E)
    (threshold : ι → ENNReal)
    (hstrip : ∀ i, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
      μ i (V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold i)
    (hmass : ∀ i, threshold i < μ i (S i))
    (hspeed : ∀ i ω, ω ∈ S i → ‖V ω‖ ≤ B)
    (hZ : ∀ i ω, ω ∈ S i → Z ω ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 2)
    (htest : ∀ i ω, ω ∈ S i →
      |fderiv ℝ g (Z ω) (spacetimeDirection (V ω))| ≤ ε)
    (hcover : ∀ x ∈ E, ∃ i, ∀ ω ∈ S i, ‖Z ω - x‖ ≤ r)
    (habsorb : (3 * A ^ J) * (1 + (B + 2) / δ) *
      (3 * (8 : ℝ) ^ J * r * (1 + 2 * B)) ≤ 1 / 2) :
    (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ g x‖ ≤ 6 * A ^ J * (1 + (B + 2) / δ) * ε) ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        |g y - g x| ≤ 12 * A ^ J * (1 + (B + 2) / δ) * ε := by
  have hApos : 0 < A := by linarith
  have hvolume := original_entry_base_volume_lower μ₀ Z E hE hApos hβ hmass₀ hcap hsupp
  have hgradient : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ g x‖ ≤ 6 * A ^ J * (1 + (B + 2) / δ) * ε := by
    have hh := gradient_renewal_from_original_broad_cells μ V hV S Z g hg E hEball
      (H := (8 : ℝ) ^ J) (A := 3 * A ^ J) (by positivity) (by positivity) hε hr hδ hB
      (fun M hM hglobal => coordinate_gradient_jets_relative_to_gradient hjets g hgext hM hglobal)
      (fun v hv hsmall => gradient_norm_from_value_jets_on_set hjets g hgext E hE hEball
        hA hvolume hv hsmall)
      threshold hstrip hmass hspeed hZ htest hcover habsorb
    intro x hx
    exact (hh x hx).trans_eq (by ring)
  refine ⟨hgradient, ?_⟩
  have hdiff (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2) :
      DifferentiableAt ℝ g z := by
    have hz4 : z ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 4 := by
      rw [mem_closedBall, dist_zero_right] at hz
      rw [mem_ball, dist_zero_right]
      linarith
    exact (hg.contDiffAt (isOpen_ball.mem_nhds hz4)).differentiableAt (by norm_num)
  intro x hx y hy
  have hx2 := closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hx
  have hy2 := closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hy
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hgradient
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2) hx2 hy2
  have hdist : ‖y - x‖ ≤ 2 := by
    have hnx : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hny : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    exact (norm_sub_le y x).trans (by linarith)
  have hn : 0 ≤ 6 * A ^ J * (1 + (B + 2) / δ) * ε := by positivity
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hdist hn)
  simpa only [Real.norm_eq_abs] using hh'.trans_eq (by ring)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
