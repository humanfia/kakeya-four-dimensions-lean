import Mathlib

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Lines with positive ordinary source duration, using the original time law. -/
def positiveSourceLines {Λ : Type*} (S : Set (Λ × ℝ)) : Set Λ :=
  {l | 0 < volume {t | (l, t) ∈ S}}

theorem measurableSet_positiveSourceLines {Λ : Type*} [MeasurableSpace Λ]
    (S : Set (Λ × ℝ)) (hS : MeasurableSet S) :
    MeasurableSet (positiveSourceLines S) := by
  exact measurableSet_lt measurable_const (measurable_measure_prodMk_left hS)

theorem exists_source_event_of_positive_line {Λ : Type*} {S : Set (Λ × ℝ)}
    {l : Λ} (hl : l ∈ positiveSourceLines S) : ∃ t, (l, t) ∈ S := by
  exact nonempty_of_measure_ne_zero (μ := volume) hl.ne'

theorem positiveSourceLines_subset {Λ : Type*} (S : Set (Λ × ℝ))
    (A : Set Λ) (hSA : ∀ e ∈ S, e.1 ∈ A) : positiveSourceLines S ⊆ A := by
  intro l hl
  obtain ⟨t, ht⟩ := exists_source_event_of_positive_line hl
  exact hSA (l, t) ht

/-- Source incidences on lines with zero source duration are null under the
original product law. No quantitative duration deletion is necessary. -/
theorem source_off_positive_lines_null {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] (S : Set (Λ × ℝ)) (hS : MeasurableSet S) :
    (ν.prod volume) (S ∩ Prod.fst ⁻¹' (positiveSourceLines S)ᶜ) = 0 := by
  have hA := measurableSet_positiveSourceLines S hS
  rw [Measure.prod_apply (hS.inter (hA.compl.preimage measurable_fst))]
  suffices hzero : ∀ l, volume (Prod.mk l ⁻¹'
      (S ∩ Prod.fst ⁻¹' (positiveSourceLines S)ᶜ)) = 0 by
    simp only [hzero, lintegral_zero]
  intro l
  by_cases hl : l ∈ positiveSourceLines S
  · have he : Prod.mk l ⁻¹' (S ∩ Prod.fst ⁻¹' (positiveSourceLines S)ᶜ) = ∅ := by
      ext t
      simp only [mem_preimage, mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
      exact fun ht => ht.2 hl
    rw [he, measure_empty]
  · apply measure_mono_null (t := {t : ℝ | (l,t) ∈ S})
    · exact fun t ht => ht.1
    · exact le_antisymm (le_of_not_gt hl) zero_le

/-- Restricting to positive-duration original lines preserves the entire source law. -/
theorem restrict_source_positive_lines {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] (S : Set (Λ × ℝ)) (hS : MeasurableSet S) :
    (ν.prod volume).restrict (S ∩ Prod.fst ⁻¹' positiveSourceLines S) =
      (ν.prod volume).restrict S := by
  have hnull := source_off_positive_lines_null ν S hS
  apply Measure.restrict_congr_set
  apply ae_eq_set.mpr
  constructor
  · exact measure_mono_null (by intro e he; exact he.2 he.1.1) (measure_empty)
  · have he : S \ (S ∩ Prod.fst ⁻¹' positiveSourceLines S) =
        S ∩ Prod.fst ⁻¹' (positiveSourceLines S)ᶜ := by
      ext e
      simp only [mem_diff, mem_inter_iff, mem_preimage, mem_compl_iff]
      tauto
    rw [he]
    exact hnull

end

end Submission.Obl.k4_physical_parent_potential_candidates
