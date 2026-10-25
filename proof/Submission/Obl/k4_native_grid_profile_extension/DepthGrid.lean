/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/DepthGrid.lean. Earlier source attributions are retained below.
-/

import Submission.Obl.k4_native_grid_profile_extension.Interface

/-! Countable compact-depth grids. -/
namespace Submission.Obl.k4_native_grid_profile_extension
open Set
def depthGrid (B : ℝ) : Set ℝ := range (Clamp B)

theorem clamp_mem {B : ℝ} (hB : 0 ≤ B) (q : ℚ) : Clamp B q ∈ Icc 0 B :=
  ⟨le_max_left _ _, max_le hB (min_le_left _ _)⟩

theorem depthGrid_countable (B : ℝ) : (depthGrid B).Countable := countable_range _

theorem zero_mem_depthGrid {B : ℝ} (hB : 0 ≤ B) : 0 ∈ depthGrid B := by
  refine ⟨0, ?_⟩
  simp only [Clamp, Rat.cast_zero, min_eq_right hB, max_self]

theorem right_mem_depthGrid {B : ℝ} (hB : 0 ≤ B) : B ∈ depthGrid B := by
  obtain ⟨q, hq⟩ := exists_rat_gt B
  exact ⟨q, by simp only [Clamp, min_eq_left hq.le, max_eq_right hB]⟩

theorem closure_depthGrid {B : ℝ} (hB : 0 ≤ B) : closure (depthGrid B) = Icc 0 B := by
  apply subset_antisymm
  · apply closure_minimal _ isClosed_Icc
    rintro x ⟨q, rfl⟩
    exact clamp_mem hB q
  · intro x hx
    let clip : ℝ → ℝ := fun t => max 0 (min B t)
    have hc : Continuous clip := by fun_prop
    have hxcl : x ∈ closure (range (fun q : ℚ => (q : ℝ))) :=
      Rat.denseRange_cast x
    have himage := image_closure_subset_closure_image (s := range (fun q : ℚ => (q : ℝ))) hc
    have hmem := himage (mem_image_of_mem clip hxcl)
    have hself : clip x = x := by
      dsimp [clip]
      rw [min_eq_right hx.2, max_eq_right hx.1]
    have heq : clip '' range (fun q : ℚ => (q : ℝ)) = depthGrid B := by
      ext y
      constructor
      · rintro ⟨t, ⟨q, rfl⟩, rfl⟩
        exact ⟨q, rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨(q : ℝ), ⟨q, rfl⟩, rfl⟩
    rw [heq, hself] at hmem
    exact hmem
end Submission.Obl.k4_native_grid_profile_extension
