/-
Adapted from: here:o204
Native/SoundReferenceCapacity.lean, session x0749. Original-reference sound-box capacity.
-/
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Basic.ENNReal.Inv

/-! Original full-reference floors and whole-entry box confinement give
capacity bounds before any later palette or output-state normalization. -/

namespace Submission.Lib.K4OriginalReferenceCapacity

open MeasureTheory Set
open scoped BigOperators

theorem sound_finite_reference_capacity {Ω J : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : J → Set Ω) (Q : Finset J) (w : J → ENNReal) (δ : ENNReal)
    (hE : ∀ j ∈ Q, MeasurableSet (E j))
    (hdisjoint : (Q : Set J).Pairwise (fun j j' => Disjoint (E j) (E j')))
    (hfloor : ∀ j ∈ Q, δ * w j ≤ μ (E j))
    (Box : Set Ω) (hsound : ∀ j ∈ Q, E j ⊆ Box) :
    δ * (∑ j ∈ Q, w j) ≤ μ Box := by
  calc
    _ = ∑ j ∈ Q, δ * w j := Finset.mul_sum ..
    _ ≤ ∑ j ∈ Q, μ (E j) := Finset.sum_le_sum (fun j hj => hfloor j hj)
    _ = μ (⋃ j ∈ Q, E j) := (measure_biUnion_finset hdisjoint hE).symm
    _ ≤ μ Box := by
      apply measure_mono
      intro x hx
      rcases mem_iUnion.mp hx with ⟨j, hx⟩
      rcases mem_iUnion.mp hx with ⟨hj, hx⟩
      exact hsound j hj hx

end Submission.Lib.K4OriginalReferenceCapacity
