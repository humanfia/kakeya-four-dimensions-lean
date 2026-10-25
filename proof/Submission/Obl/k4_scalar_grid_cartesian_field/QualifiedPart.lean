import Mathlib

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory

/-- Removing a measurable hull of the bad set leaves pointwise qualified incidences.
Its cost is exactly the original outer mass used in the qualification hypothesis. -/
theorem measurable_part_avoiding_bad {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E Bad : Set Ω) (hE : MeasurableSet E) :
    ∃ Good : Set Ω, MeasurableSet Good ∧ Good ⊆ E ∧
      (∀ p ∈ Good, p ∉ Bad) ∧ μ E ≤ μ Good + μ Bad := by
  let V := toMeasurable μ Bad
  refine ⟨E \ V, hE.diff (measurableSet_toMeasurable μ Bad), diff_subset, ?_, ?_⟩
  · intro p hp hbad
    exact hp.2 (subset_toMeasurable μ Bad hbad)
  · calc
      _ ≤ μ ((E \ V) ∪ V) := by
        apply measure_mono
        intro p hp
        by_cases hv : p ∈ V
        · exact Or.inr hv
        · exact Or.inl ⟨hp, hv⟩
      _ ≤ μ (E \ V) + μ V := measure_union_le _ _
      _ = _ := by rw [show μ V = μ Bad from measure_toMeasurable Bad]

/-- Shrinking a packet by an a.e. coefficient bound preserves its unchanged full prior mass. -/
theorem packet_inter_conull_mass {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (A C : Set Ω) (hC : ν Cᶜ = 0) : ν (A ∩ C) = ν A :=
  measure_inter_conull hC

end Submission.Obl.k4_scalar_grid_cartesian_field
