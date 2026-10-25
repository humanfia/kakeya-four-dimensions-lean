-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.MarginalFloors

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Finset

noncomputable section

/-- Simultaneous positive incidence floors for a finite family of measurable
labels. The labels may overlap. Only incidences are removed; the supplied
thresholds, full assignments and reference law stay fixed. The finite
maximization argument is the measure version of `exists_simultaneous_marginal_floors`
(adapted there from o107/x0735). -/
theorem exists_simultaneous_incidence_floors
    {Y J : Type*} [MeasurableSpace Y] [Fintype J]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (U : Set Y) (hU : MeasurableSet U)
    (cells : J → Set Y) (hcells : ∀ j, MeasurableSet (cells j))
    (threshold : J → ℝ) (hthreshold : ∀ j, 0 ≤ threshold j) :
    ∃ E : Set Y, MeasurableSet E ∧ E ⊆ U ∧
      μ.real U - (∑ j, threshold j) ≤ μ.real E ∧
      ∀ j, (E ∩ cells j).Nonempty → threshold j ≤ μ.real (E ∩ cells j) := by
  classical
  let rem : Finset J → Set Y := fun d => U \ ⋃ j ∈ d, cells j
  let active : Set Y → Finset J := fun E => univ.filter (fun j => (E ∩ cells j).Nonempty)
  let penalty : Set Y → ℝ := fun E => ∑ j ∈ active E, threshold j
  let score : Set Y → ℝ := fun E => μ.real E - penalty E
  obtain ⟨d, hd, hmax⟩ := exists_max_image (univ : Finset J).powerset (fun d => score (rem d))
    ⟨∅, mem_powerset.mpr (empty_subset _)⟩
  let E := rem d
  have hm (d : Finset J) : MeasurableSet (rem d) :=
    hU.diff (.biUnion d.countable_toSet (fun j _ => hcells j))
  refine ⟨E, hm d, sdiff_subset, ?_, ?_⟩
  · have hm := hmax ∅ (mem_powerset.mpr (empty_subset _))
    have hpenU : penalty U ≤ ∑ j, threshold j :=
      sum_le_sum_of_subset_of_nonneg (subset_univ (active U)) (fun j _ _ => hthreshold j)
    have hpenE : 0 ≤ penalty E := sum_nonneg fun j _ => hthreshold j
    have hrem : rem ∅ = U := by simp [rem]
    rw [hrem] at hm
    change μ.real U - penalty U ≤ μ.real E - penalty E at hm
    linarith
  · intro j hj
    by_contra hnot
    have hlight : μ.real (E ∩ cells j) < threshold j := lt_of_not_ge hnot
    let V := E \ cells j
    have hVS : V ⊆ E := sdiff_subset
    have hrem : rem (insert j d) = V := by
      ext y
      simp only [rem, Set.mem_sdiff, Set.mem_iUnion, exists_prop, Finset.mem_insert, V, E]
      aesop
    have hmaxV := hmax (insert j d) (mem_powerset.mpr (subset_univ _))
    rw [hrem] at hmaxV
    have hjactive : j ∈ active E := mem_filter.mpr ⟨mem_univ j, hj⟩
    have hactive : active V ⊆ active E := by
      intro k hk
      obtain ⟨y, hy⟩ := (mem_filter.mp hk).2
      exact mem_filter.mpr ⟨mem_univ k, ⟨y, hVS hy.1, hy.2⟩⟩
    have hjnot : j ∉ active V := by
      intro h
      obtain ⟨y, hy⟩ := (mem_filter.mp h).2
      exact hy.1.2 hy.2
    have hpen : penalty V + threshold j ≤ penalty E := by
      have hsub : insert j (active V) ⊆ active E := insert_subset_iff.mpr ⟨hjactive, hactive⟩
      have hsum := sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hthreshold k)
      rw [sum_insert hjnot] at hsum
      simpa only [penalty, add_comm] using hsum
    have hmass : μ.real V + μ.real (E ∩ cells j) = μ.real E :=
      measureReal_sdiff_add_inter (hcells j) (measure_ne_top μ E)
    change μ.real V - penalty V ≤ μ.real E - penalty E at hmaxV
    linarith

end

end Submission.Obl.k4_finite_affine_parent_sources
