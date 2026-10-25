import Mathlib

namespace Submission.Obl.k4_algebraic_sheet_bound

open Set Metric

/-- A continuous chosen root stays inside a root-free circle on a connected set. -/
theorem norm_lt_of_root_free_circle {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s) {f : X → ℂ} (hf : ContinuousOn f s)
    {Q : X → ℂ → ℂ} (hroot : ∀ x ∈ s, Q x (f x) = 0)
    {R : ℝ} (hfree : ∀ x ∈ s, ∀ w : ℂ, ‖w‖ = R → Q x w ≠ 0)
    {a : X} (ha : a ∈ s) (hfa : ‖f a‖ < R) :
    ∀ x ∈ s, ‖f x‖ < R := by
  intro x hx
  by_contra h
  obtain ⟨y, hy, hfy⟩ := hs.intermediate_value ha hx hf.norm
    (show R ∈ Set.Icc ‖f a‖ ‖f x‖ from ⟨hfa.le, le_of_not_gt h⟩)
  exact hfree y hy (f y) hfy (hroot y hy)

/-- A root-free circle on a connected set containing a boundary circle controls the disk. -/
theorem norm_le_on_disk_of_root_free_circle {f : ℂ → ℂ} {Q : ℂ → ℂ → ℂ}
    {s : Set ℂ} (hs : IsPreconnected s) {r R : ℝ} (hr : 0 < r)
    (hcircle : sphere (0 : ℂ) r ⊆ s)
    (hcont : ContinuousOn f s) (hroot : ∀ x ∈ s, Q x (f x) = 0)
    (hfree : ∀ x ∈ s, ∀ w : ℂ, ‖w‖ = R → Q x w ≠ 0)
    {a : ℂ} (ha : a ∈ s) (hfa : ‖f a‖ < R)
    (hdiff : DiffContOnCl ℂ f (ball 0 r)) {z : ℂ} (hz : z ∈ closedBall 0 r) :
    ‖f z‖ ≤ R := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff
  · intro w hw
    exact (norm_lt_of_root_free_circle hs hcont hroot hfree ha hfa w
      (hcircle (frontier_ball_subset_sphere hw))).le
  · simpa only [closure_ball (0 : ℂ) hr.ne'] using hz

end Submission.Obl.k4_algebraic_sheet_bound
