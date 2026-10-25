import Mathlib

/-!
# Quantitative local injectivity

A lower bound for the derivative, together with a modulus for its variation,
gives an injectivity radius. This lets the matching proof use a polynomial
number of small injective pieces rather than a semialgebraic fiber theorem.
-/

namespace Submission.Obl.k4_two_color_matching

open Set
open scoped NNReal

/-- The mean value inequality gives injectivity when the derivative stays
closer to one linear map than that map's lower norm bound. -/
lemma injOn_of_fderiv_close
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} (hS : Convex ℝ S)
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) (A : E →L[ℝ] F)
    {ε δ : ℝ} (hεδ : ε < δ)
    (hA : ∀ v : E, δ * ‖v‖ ≤ ‖A v‖)
    (hclose : ∀ x ∈ S, ‖fderiv ℝ f x - A‖ ≤ ε) : InjOn f S := by
  intro x hx y hy hxy
  have hmv := hS.norm_image_sub_le_of_norm_fderiv_le' hf hclose hx hy
  have hu : ‖A (y - x)‖ ≤ ε * ‖y - x‖ := by
    simpa only [hxy, sub_self, zero_sub, norm_neg] using hmv
  have hlo := hA (y - x)
  have hn : ‖y - x‖ = 0 := by
    have hnonneg := norm_nonneg (y - x)
    nlinarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

lemma injOn_closedBall_of_lipschitz_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {r δ : ℝ} (L : ℝ≥0)
    (hf : ∀ y ∈ Metric.closedBall x r, DifferentiableAt ℝ f y)
    (hlip : LipschitzOnWith L (fderiv ℝ f) (Metric.closedBall x r))
    (hr : 0 ≤ r) (hsmall : (L : ℝ) * r < δ)
    (hlower : ∀ v : E, δ * ‖v‖ ≤ ‖fderiv ℝ f x v‖) :
    InjOn f (Metric.closedBall x r) := by
  apply injOn_of_fderiv_close (convex_closedBall x r) hf (fderiv ℝ f x) hsmall hlower
  intro y hy
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr
  have hbound := hlip.norm_sub_le hy hx
  have hy' : ‖y - x‖ ≤ r := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hy
  exact hbound.trans (mul_le_mul_of_nonneg_left hy'
    (show (0 : ℝ) ≤ L from L.coe_nonneg))

end Submission.Obl.k4_two_color_matching
