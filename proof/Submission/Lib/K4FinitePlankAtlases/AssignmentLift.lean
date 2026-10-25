import Submission.Lib.K4FinitePlankAtlases.Assignments

/-!
Adapted from: here:o049

Original proof developed by session x0147 in
Submission/Obl/k4_cap_class_terminal_charts/AssignmentLift.lean.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open MeasureTheory Set

/-- Priority assignment commutes with every change of trajectory domain. -/
theorem firstAssignment_preimage {α β : Type*} {m : ℕ}
    (f : α → β) (S : Fin m → Set β) (i : Fin m) :
    f ⁻¹' firstAssignment S i = firstAssignment (fun j => f ⁻¹' S j) i := rfl

/-- Internal measurable restrictions may be used to locate the chart constants.
Its final assignment can then be a geometric priority fit clipped by a formatted
eligibility test; no internal mask needs to appear in that assignment. -/
theorem priority_mass_lift_through_clip {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {m : ℕ}
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure ν]
    (f : α → β) (hf : Measurable f) (hdom : μ.map f ≤ ν)
    (S T : Fin m → Set β) (hS : ∀ i, MeasurableSet (S i))
    (hT : ∀ i, MeasurableSet (T i)) (i : Fin m)
    (hclip : ∀ x ∈ firstAssignment (fun j => f ⁻¹' S j) i, f x ∈ T i) :
    μ.real (firstAssignment (fun j => f ⁻¹' S j) i) ≤
      ν.real (firstAssignment S i ∩ T i) := by
  have htarget : MeasurableSet (firstAssignment S i ∩ T i) :=
    (measurableSet_firstAssignment S hS i).inter (hT i)
  have hsub : firstAssignment (fun j => f ⁻¹' S j) i ⊆
      f ⁻¹' (firstAssignment S i ∩ T i) := by
    intro x hx
    refine ⟨?_, hclip x hx⟩
    change x ∈ f ⁻¹' firstAssignment S i
    rw [firstAssignment_preimage]
    exact hx
  have hmass : μ (firstAssignment (fun j => f ⁻¹' S j) i) ≤
      ν (firstAssignment S i ∩ T i) := by
    calc
      _ ≤ μ (f ⁻¹' (firstAssignment S i ∩ T i)) := measure_mono hsub
      _ = μ.map f (firstAssignment S i ∩ T i) := (Measure.map_apply hf htarget).symm
      _ ≤ _ := hdom _
  exact ENNReal.toReal_mono (measure_ne_top ν _) hmass

/-- The case with no additional clipping preserves every original-law floor. -/
theorem priority_mass_lift {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {m : ℕ}
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure ν]
    (f : α → β) (hf : Measurable f) (hdom : μ.map f ≤ ν)
    (S : Fin m → Set β) (hS : ∀ i, MeasurableSet (S i)) (i : Fin m) :
    μ.real (firstAssignment (fun j => f ⁻¹' S j) i) ≤ ν.real (firstAssignment S i) := by
  simpa only [inter_univ] using priority_mass_lift_through_clip μ ν f hf hdom S
    (fun _ => univ) hS (fun _ => MeasurableSet.univ) i (fun _ _ => mem_univ _)

end Submission.Lib.K4FinitePlankAtlases
