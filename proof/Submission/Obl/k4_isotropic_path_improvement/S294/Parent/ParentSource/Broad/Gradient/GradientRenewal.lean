-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.GradientRenewal, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/GradientRenewal.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/GradientRenewal.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/GradientRenewal.lean. Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/GradientRenewal.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.HessianCoordinates

/-! # Absorb relative Hessian errors using original broad cell tests -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric

noncomputable section

/-- Algebraic coordinate norming and ORIGINAL broad cell tests bound the
whole residual gradient. The Hessian is derived from the coordinate jets
of the same function and the actual maximum gradient; no independent
Hessian witness or later selected-entry mass is assumed. -/
theorem gradient_renewal_from_original_broad_cells
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : ι → Measure Ω) (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V)
    (S : ι → Set Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3))
    (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : ContDiffOn ℝ 2 g (ball 0 4))
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hEball : E ⊆ closedBall 0 1)
    {H A ε r δ B : ℝ} (hH : 0 ≤ H) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hcoordinate_norming : ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2, ‖fderiv ℝ g x‖ ≤ M) →
      ∀ j : Fin 3, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        ‖fderiv ℝ (gradientComponent g j) x‖ ≤ H * M)
    (horiginal_norming : ∀ v : ℝ, 0 ≤ v →
      (∀ x ∈ E, ‖fderiv ℝ g x‖ ≤ v) →
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2, ‖fderiv ℝ g x‖ ≤ A * v)
    (threshold : ι → ENNReal)
    (hstrip : ∀ i, ∀ n : EuclideanSpace ℝ (Fin 2), ‖n‖ = 1 → ∀ c : ℝ,
      μ i (V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip n c δ) ≤ threshold i)
    (hmass : ∀ i, threshold i < μ i (S i))
    (hspeed : ∀ i ω, ω ∈ S i → ‖V ω‖ ≤ B)
    (hZ : ∀ i ω, ω ∈ S i → Z ω ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 2)
    (htest : ∀ i ω, ω ∈ S i →
      |fderiv ℝ g (Z ω) (spacetimeDirection (V ω))| ≤ ε)
    (hcover : ∀ x ∈ E, ∃ i, ∀ ω ∈ S i, ‖Z ω - x‖ ≤ r)
    (habsorb : A * (1 + (B + 2) / δ) * (3 * H * r * (1 + 2 * B)) ≤ 1 / 2) :
    ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ g x‖ ≤ 2 * A * (1 + (B + 2) / δ) * ε := by
  obtain ⟨M, hM, hglobal, xmax, hxmax, hmax⟩ := exists_core_gradient_max g hg
  let C := 1 + (B + 2) / δ
  let D := 3 * H * r * (1 + 2 * B)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hdfsm : ContDiffOn ℝ 1 (fderiv ℝ g) (ball 0 4) :=
    hg.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hdf (x : EuclideanSpace ℝ (Fin 3))
      (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2) :
      DifferentiableAt ℝ (fderiv ℝ g) x := by
    have hx4 : x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 4 := by
      rw [mem_closedBall, dist_zero_right] at hx
      rw [mem_ball, dist_zero_right]
      linarith
    exact (hdfsm.contDiffAt (isOpen_ball.mem_nhds hx4)).differentiableAt (by norm_num)
  have hsecond : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖iteratedFDeriv ℝ 2 g x‖ ≤ 3 * (H * M) := by
    intro x hx
    exact hessian_norm_le_coordinate_gradients g x (hdf x (ball_subset_closedBall hx))
      (mul_nonneg hH hM) (fun j => hcoordinate_norming M hM hglobal j x (ball_subset_closedBall hx))
  have hpoint : ∀ x ∈ E, ‖fderiv ℝ g x‖ ≤ C * (ε + D * M) := by
    intro x hx
    have hx2 : x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 2 := by
      have hh := hEball hx
      rw [mem_closedBall, dist_zero_right] at hh
      rw [mem_ball, dist_zero_right]
      linarith
    obtain ⟨i, hnear⟩ := hcover x hx
    have hh := gradient_bound_from_second_jet_and_original_tests (μ i) V hV (S i)
      g Z x (ball 0 2) isOpen_ball (convex_ball _ _)
      (hg.mono (ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4))) hx2
      (hZ i) (fun _ => 0) (δ := δ) (K := 0) (E := ε) (M := 3 * (H * M))
      (r := r) (B := B) (threshold := threshold i)
      hδ (by norm_num) hε (by positivity) hr hB hsecond hnear (hstrip i) (hmass i)
      (hspeed i) (by intros; simp) (by
        intro ω hω
        simpa only [sub_zero] using htest i ω hω)
    convert hh.2 using 1 <;> dsimp only [C, D] <;> ring
  have hnorm := horiginal_norming (C * (ε + D * M)) (by positivity) hpoint
  have hmain : M ≤ A * C * (ε + D * M) := by
    calc
      M = ‖fderiv ℝ g xmax‖ := hmax
      _ ≤ A * (C * (ε + D * M)) := hnorm xmax hxmax
      _ = _ := by ring
  change A * C * D ≤ 1 / 2 at habsorb
  have hsmall := mul_le_mul_of_nonneg_right habsorb hM
  have hbound : M ≤ 2 * A * C * ε := by nlinarith
  intro x hx
  exact (hglobal x hx).trans hbound

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
