import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory
open scoped ENNReal

/-- Disjoint old source sets assigned to one chart charge only that chart's
original, unnormalized incidence mass. -/
theorem merged_fiber_mass_le {X ι C : Type*}
    [MeasurableSpace X] [Fintype ι] [DecidableEq C]
    (μ : Measure X) (tag : ι → C) (A : ι → Set X) (F : C → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i j, i ≠ j → tag i = tag j → Disjoint (A i) (A j))
    (hsub : ∀ i, A i ⊆ F (tag i)) (b : C) :
    (∑ i ∈ Finset.univ.filter (fun i => tag i = b), μ (A i)) ≤ μ (F b) := by
  have h := Submission.Obl.k4_quadratic_atlas_normalization.sum_measure_assignment_fiber_le
    (μ.restrict (F b)) tag A b hA hdisj
  simpa only [Measure.restrict_apply_univ] using
    (show (∑ i ∈ Finset.univ.filter (fun i => tag i = b), μ (A i)) ≤
        (μ.restrict (F b)) univ from by
      convert h using 1
      apply Finset.sum_congr rfl
      intro i hi
      have htag := (Finset.mem_filter.mp hi).2
      rw [Measure.restrict_apply (hA i)]
      have hs : A i ⊆ F b := by simpa only [htag] using hsub i
      rw [inter_eq_left.mpr hs])

/-- Merging source sections along a finite representative table preserves the
sum of their original weighted incidence masses. -/
theorem weighted_merged_mass_le {X ι C : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype C] [DecidableEq C]
    (μ : C → Measure X) (w : C → ℝ≥0∞) (tag : ι → C)
    (A : ι → Set X) (F : C → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i j, i ≠ j → tag i = tag j → Disjoint (A i) (A j))
    (hsub : ∀ i, A i ⊆ F (tag i)) :
    (∑ i, w (tag i) * μ (tag i) (A i)) ≤ ∑ b, w b * μ b (F b) := by
  have heq : (∑ i, w (tag i) * μ (tag i) (A i)) =
      ∑ b, w b * ∑ i ∈ Finset.univ.filter (fun i => tag i = b), μ b (A i) := by
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  rw [heq]
  apply Finset.sum_le_sum
  intro b _
  gcongr
  exact merged_fiber_mass_le (μ b) tag A F hA hdisj hsub b

end Submission.Obl.k4_pair_bin_atlas_assembly
