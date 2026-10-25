-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.GradientCaptureAlternative, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/GradientCaptureAlternative.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit af69463910936c02b3e287e9153c4781be3e7639,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/GradientCaptureAlternative.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.GradientStripPrediction

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric
open scoped RealInnerProductSpace

noncomputable section

/-- At any registered depth, actual directional tests give either a
whole-core gradient bound or a table of thin strips capturing all but
one ORIGINAL entry floor. Relative Hessian control is derived from the
value-jet hypothesis and absorbed against the actual maximum gradient.
No velocity breadth at this depth is assumed. -/
theorem original_entry_gradient_or_strip_capture
    {D J : ℕ} (hjets : ValueJetBound D J)
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3))
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V)
    (S : Set Ω) (hS : MeasurableSet S) (state : Ω → I)
    (hstate : ∀ i, MeasurableSet (state ⁻¹' {i}))
    (region : I → Set (EuclideanSpace ℝ (Fin 3)))
    (hregion : ∀ i, MeasurableSet (region i))
    (hball : ∀ i, region i⊆closedBall 0 1)
    (hZ : ∀ ω∈S, Z ω∈region (state ω))
    (anchor : I → EuclideanSpace ℝ (Fin 3))
    (hanchor : ∀ i, anchor i∈closedBall 0 1)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : ContDiffOn ℝ 2 g (ball 0 4))
    (hgext : ∀ j : Fin 3, exf D (gradientComponent g j))
    {A β δ E r B : ℝ} (hA : 2 ≤ A) (hβ : 0 < β)
    (hδ : 0 < δ) (hE : 0 ≤ E) (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hcap : ∀ U, MeasurableSet U → μ (Z ⁻¹' U) ≤ ENNReal.ofReal β*volume U)
    (hnear : ∀ i x, x∈region i → ‖x-anchor i‖ ≤ r)
    (hspeed : ∀ ω∈S, ‖V ω‖ ≤ B)
    (htest : ∀ ω∈S, |fderiv ℝ g (Z ω) (spacetimeDirection (V ω))| ≤ E)
    (habsorb : (3*A^J)*((1+(B+2)/δ)*(1+2*B)+1)*
      (3*(8:ℝ)^J*r) ≤ 1/2) :
    (∀ x∈closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ g x‖ ≤ 6*A^J*(1+(B+2)/δ)*E) ∨
    ∃ (normal : I → EuclideanSpace ℝ (Fin 2)) (center : I → ℝ),
      (∀ i, ‖normal i‖=1 ∧ |center i| ≤ B+δ) ∧
      MeasurableSet (⋃ i, state ⁻¹' {i}∩
        V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) δ) ∧
      μ (S\⋃ i, state ⁻¹' {i}∩
        V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) δ) <
          ENNReal.ofReal (β/A) := by
  classical
  by_cases hgood : ∀ x∈closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ g x‖ ≤ 6*A^J*(1+(B+2)/δ)*E
  · exact Or.inl hgood
  right
  obtain ⟨M,hM,hglobal,xmax,hxmax,hmax⟩ := exists_core_gradient_max g hg
  let C := 1+(B+2)/δ
  let T := 3*(8:ℝ)^J*r
  let e := T*M
  have he : 0 ≤ e := by dsimp [e,T]; positivity
  have hbad : 6*A^J*C*E < M := by
    by_contra h
    have hle : M ≤ 6*A^J*C*E := le_of_not_gt h
    exact hgood (fun x hx => (hglobal x hx).trans hle)
  have hdfsm : ContDiffOn ℝ 1 (fderiv ℝ g) (ball 0 4) :=
    hg.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hdf (x : EuclideanSpace ℝ (Fin 3)) (hx : x∈closedBall 0 2) :
      DifferentiableAt ℝ (fderiv ℝ g) x := by
    have hx4 : x∈ball (0 : EuclideanSpace ℝ (Fin 3)) 4 := by
      rw [mem_closedBall,dist_zero_right] at hx
      rw [mem_ball,dist_zero_right]
      linarith
    exact (hdfsm.contDiffAt (isOpen_ball.mem_nhds hx4)).differentiableAt (by norm_num)
  have hsecond : ∀ x∈ball (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖iteratedFDeriv ℝ 2 g x‖ ≤ 3*((8:ℝ)^J*M) := by
    intro x hx
    exact hessian_norm_le_coordinate_gradients g x (hdf x (ball_subset_closedBall hx))
      (by positivity) (fun j => coordinate_gradient_jets_relative_to_gradient
        hjets g hgext hM hglobal j x (ball_subset_closedBall hx))
  have hfreeze (i) (x) (hx : x∈region i) :
      ‖fderiv ℝ g x-fderiv ℝ g (anchor i)‖ ≤ e := by
    have hsub : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1⊆ball 0 2 :=
      closedBall_subset_ball (by norm_num)
    calc
      _ ≤ (3*((8:ℝ)^J*M))*‖x-anchor i‖ :=
        derivative_freeze_of_second_jet g (ball 0 2) isOpen_ball (convex_ball _ _)
          (hg.mono (ball_subset_ball (by norm_num : (2:ℝ) ≤ 4))) hsecond
          (hsub (hanchor i)) (hsub (hball i hx))
      _ ≤ (3*((8:ℝ)^J*M))*r :=
        mul_le_mul_of_nonneg_left (hnear i x hx) (by positivity)
      _ = e := by dsimp [e,T]; ring
  have hlarge : 3*A^J*((E+e+B*(2*e))+(B+2)*((E+e+B*(2*e))/δ)+e) <
      ‖fderiv ℝ g xmax‖ := by
    have herror : (3*A^J)*(C*(1+2*B)+1)*T*M ≤ M/2 := by
      have hh := mul_le_mul_of_nonneg_right habsorb hM
      change (3*A^J)*(C*(1+2*B)+1)*T*M ≤ (1/2)*M at hh
      simpa only [one_div,one_mul,mul_comm (2:ℝ)⁻¹ M,div_eq_mul_inv] using hh
    rw [←hmax]
    calc
      _ = 3*A^J*C*E+(3*A^J)*(C*(1+2*B)+1)*T*M := by
        dsimp [C,e]
        ring
      _ ≤ 3*A^J*C*E+M/2 := add_le_add le_rfl herror
      _ < M := by nlinarith
  exact original_entry_large_gradient_strip_capture hjets μ Z V hV S hS state hstate
    region hregion hball hZ g hgext (fun i => fderiv ℝ g (anchor i)) hA hβ hδ hE he hB
    hcap hfreeze hspeed htest ⟨xmax,hxmax,hlarge⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
