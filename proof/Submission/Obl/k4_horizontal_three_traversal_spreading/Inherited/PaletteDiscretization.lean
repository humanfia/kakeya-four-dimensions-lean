-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/PaletteDiscretization.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/PaletteDiscretization.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Mathlib

/-! Finite reference palettes retain their original probability weights. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical Set MeasureTheory

variable {Pal : Type*} [Fintype Pal] [DecidableEq Pal]

/-- A finite subfamily of disjoint palette atoms has total mass at most one.
The unrepresented tail of the original palette is left out. -/
theorem finite_palette_weights_subprob
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (C : Pal → Set ℝ)
    (hmeas : ∀ z, MeasurableSet (C z))
    (hdisj : Pairwise (fun z w => Disjoint (C z) (C w))) :
    (∑ z, μ.real (C z)) ≤ 1 := by
  calc
    _ = μ.real (⋃ z ∈ (univ : Finset Pal), C z) :=
      (measureReal_biUnion_finset (μ := μ) (fun _ _ _ _ hne => hdisj hne)
        (fun z _ => hmeas z)).symm
    _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
    _ = _ := by simp

/-- Rounding a palette coordinate by at most delta enlarges every interval
test by delta, with no change in the original weights. -/
theorem finite_palette_near_weight
    (μ : Measure ℝ) [IsFiniteMeasure μ] (C : Pal → Set ℝ) (vel : Pal → ℝ)
    (hmeas : ∀ z, MeasurableSet (C z))
    (hdisj : Pairwise (fun z w => Disjoint (C z) (C w)))
    (δ r v : ℝ) (hnear : ∀ z x, x ∈ C z → |x - vel z| ≤ δ) :
    (∑ z ∈ univ.filter (fun z => |vel z - v| ≤ r), μ.real (C z)) ≤
      μ.real (Set.Icc (v - (r + δ)) (v + (r + δ))) := by
  let B : Finset Pal := univ.filter (fun z => |vel z - v| ≤ r)
  have hsubset : (⋃ z ∈ B, C z) ⊆ Set.Icc (v - (r + δ)) (v + (r + δ)) := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
    have hz' := (mem_filter.mp hz).2
    have hdist : |x - v| ≤ r + δ :=
      (abs_sub_le x (vel z) v).trans (by linarith [hnear z x hxz])
    exact ⟨by linarith [(abs_le.mp hdist).1], by linarith [(abs_le.mp hdist).2]⟩
  calc
    _ = μ.real (⋃ z ∈ B, C z) :=
      (measureReal_biUnion_finset (μ := μ) (fun _ _ _ _ hne => hdisj hne)
        (fun z _ => hmeas z)).symm
    _ ≤ _ := measureReal_mono hsubset

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
