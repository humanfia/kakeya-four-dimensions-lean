-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/RepresentativeLists.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.JetLabels

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Finset Submission.Lib.K4OriginalLists

variable {ι α X : Type*} [Fintype ι] [Fintype α] [MeasurableSpace X]

theorem mergedLabel_binRepresentative (width : ι → ℝ) (jet : α → ι → ℝ)
    (b : binLabels width jet) : mergedLabel width jet (binRepresentative width jet b) = b := by
  apply Subtype.ext
  exact binRepresentative_spec width jet b

theorem binRepresentative_injective (width : ι → ℝ) (jet : α → ι → ℝ) :
    Function.Injective (binRepresentative width jet) := by
  intro b b' h
  have he := congrArg (mergedLabel width jet) h
  simpa only [mergedLabel_binRepresentative] using he

/-- The actual representative index of the merged label of an entry. -/
noncomputable def representativeOf (width : ι → ℝ) (jet : α → ι → ℝ) (a : α) : α :=
  binRepresentative width jet (mergedLabel width jet a)

theorem representativeOf_idempotent (width : ι → ℝ) (jet : α → ι → ℝ) (a : α) :
    representativeOf width jet (representativeOf width jet a) = representativeOf width jet a := by
  simp only [representativeOf, mergedLabel_binRepresentative]

/-- Lists of bins become lists of actual entries, with the same cardinality. -/
noncomputable def representativeLists (width : ι → ℝ) (jet : α → ι → ℝ)
    (L : X → Finset (binLabels width jet)) (x : X) : Finset α := by
  classical
  exact (L x).image (binRepresentative width jet)

theorem mem_representativeLists (width : ι → ℝ) (jet : α → ι → ℝ)
    (L : X → Finset (binLabels width jet)) (x : X) (a : α) :
    a ∈ representativeLists width jet L x ↔
      representativeOf width jet a = a ∧ mergedLabel width jet a ∈ L x := by
  classical
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simp only [representativeOf, mergedLabel_binRepresentative]
    exact ⟨trivial, hb⟩
  · rintro ⟨ha, hlabel⟩
    exact Finset.mem_image.mpr ⟨mergedLabel width jet a, hlabel, ha⟩

theorem representative_mem_representativeLists (width : ι → ℝ) (jet : α → ι → ℝ)
    (L : X → Finset (binLabels width jet)) (x : X) (a : α) :
    representativeOf width jet a ∈ representativeLists width jet L x ↔
      mergedLabel width jet a ∈ L x := by
  rw [mem_representativeLists, representativeOf_idempotent]
  simp only [true_and, representativeOf, mergedLabel_binRepresentative]

theorem measurable_representativeLists (width : ι → ℝ) (jet : α → ι → ℝ)
    (L : X → Finset (binLabels width jet)) (hL : MeasurableLists L) :
    MeasurableLists (representativeLists width jet L) := by
  intro a
  by_cases ha : representativeOf width jet a = a
  · convert hL (mergedLabel width jet a) using 1
    ext x
    simp only [Set.mem_ofPred_eq, mem_representativeLists, ha, true_and]
  · have he : {x | a ∈ representativeLists width jet L x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_representativeLists, ha, false_and, Set.mem_empty_iff_false]
    rw [he]
    exact MeasurableSet.empty

theorem card_representativeLists (width : ι → ℝ) (jet : α → ι → ℝ)
    (L : X → Finset (binLabels width jet)) (x : X) :
    (representativeLists width jet L x).card = (L x).card := by
  classical
  exact Finset.card_image_of_injective _ (binRepresentative_injective width jet)

/-- Changing the output labels to actual representative entries preserves each
original component's entire success event, hence its unnormalized success mass. -/
theorem representativeLists_success_mass {Z : Type*} [MeasurableSpace Z]
    (width : ι → ℝ) (jet : α → ι → ℝ) (L : X → Finset (binLabels width jet))
    (μ : Measure Z) (O : Z → X) (a : α) :
    μ {z | representativeOf width jet a ∈ representativeLists width jet L (O z)} =
      μ {z | mergedLabel width jet a ∈ L (O z)} := by
  congr 1
  ext z
  exact representative_mem_representativeLists width jet L (O z) a

end Submission.Obl.k4_clean_cover_graph_atlas
