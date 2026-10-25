import Submission.Obl.k4_scalar_candidate_original_return.Core.Prune

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Whole original assignments can be pruned against any summable reference
thresholds. This specializes the accepted finite simultaneous-pruning theorem
to a single family, before normalizing any chart. -/
theorem select_heavy_assignments {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [DecidableEq ι] (ζ : Measure (α × ℝ)) [IsFiniteMeasure ζ]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) (thr : ι → ENNReal) :
    ∃ S : Finset ι,
      (∀ i ∈ S, thr i ≤ ζ (A i ×ˢ univ)) ∧
      ζ {p | ∃ i, p.1 ∈ A i} ≤ ζ {p | ∃ i ∈ S, p.1 ∈ A i} + ∑ i, thr i := by
  classical
  let region : ι → Set (α × ℝ) := fun i => A i ×ˢ univ
  have hregion : ∀ i, MeasurableSet (region i) := fun i => (hA i).prod MeasurableSet.univ
  have : ∀ _g : Unit, IsFiniteMeasure ((fun _ : Unit => ζ) _g) := fun _ => inferInstance
  obtain ⟨S, hfloor, hbudget⟩ :=
    Submission.Obl.k4_scalar_candidate_original_return.Prune.exists_pruned
      (fun _ : ι => ()) (fun _ : ι => ()) region hregion (fun _ : Unit => ζ) thr
  have hsupp (S : Finset ι) :
      Submission.Obl.k4_scalar_candidate_original_return.Prune.support
        (fun _ : ι => ()) (fun _ : ι => ()) region S () =
        {p : α × ℝ | ∃ i ∈ S, p.1 ∈ A i} := by
    ext p
    rw [Submission.Obl.k4_scalar_candidate_original_return.Prune.mem_support]
    simp [region]
  refine ⟨S, ?_, ?_⟩
  · intro i hi
    exact (hfloor i hi).trans (Measure.restrict_le_self _)
  · simpa [hsupp] using hbudget ()

end Submission.Obl.k4_horizontal_supercritical_three_projections
