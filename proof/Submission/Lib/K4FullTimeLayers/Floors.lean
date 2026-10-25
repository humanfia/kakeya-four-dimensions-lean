import Mathlib

/-!
Adapted from: here:o217
Original proofs by x0759, SimultaneousFloors.lean, commit e3de39a3.
-/

namespace Submission.Lib.K4FullTimeLayers

open MeasureTheory Set
open scoped ENNReal

/-- Iterated light-label deletion charges each label only once. The final
restriction has all the requested floors at the same time. -/
theorem simultaneous_floor_restriction {Ω ι : Type*} [MeasurableSpace Ω]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (w : ι → ℝ≥0∞)
    (s : Finset ι) (μ : Measure Ω) :
    ∃ E : Set Ω, MeasurableSet E ∧
      μ univ ≤ μ E + ∑ i ∈ s, w i ∧
      ∀ i ∈ s, μ (E ∩ A i) = 0 ∨ w i ≤ μ (E ∩ A i) := by
  classical
  induction s using Finset.strongInductionOn generalizing μ
  rename_i s ih
  by_cases hgood : ∀ i ∈ s, μ (A i) = 0 ∨ w i ≤ μ (A i)
  · exact ⟨univ, MeasurableSet.univ, le_add_right le_rfl, by simpa using hgood⟩
  · push Not at hgood
    obtain ⟨i, hi, hzero, hlight⟩ := hgood
    let μ' := μ.restrict (A i)ᶜ
    obtain ⟨E, hE, hmass, hfloor⟩ := ih (s.erase i) (Finset.erase_ssubset hi) μ'
    refine ⟨E ∩ (A i)ᶜ, hE.inter (hA i).compl, ?_, ?_⟩
    · have hsplit : μ univ = μ' univ + μ (A i) := by
        rw [Measure.restrict_apply_univ]
        exact (measure_add_measure_compl (hA i)).symm.trans (by ac_rfl)
      have hME : μ' E = μ (E ∩ (A i)ᶜ) := Measure.restrict_apply hE
      calc
        μ univ = μ' univ + μ (A i) := hsplit
        _ ≤ (μ' E + ∑ j ∈ s.erase i, w j) + w i :=
          add_le_add hmass (le_of_lt hlight)
        _ = μ (E ∩ (A i)ᶜ) + ∑ j ∈ s, w j := by
          rw [hME, add_assoc, Finset.sum_erase_add _ _ hi]
    · intro j hj
      by_cases hji : j = i
      · left
        subst j
        have hempty : (E ∩ (A i)ᶜ) ∩ A i = ∅ := by aesop
        rw [hempty, measure_empty]
      · have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
        have heq : μ' (E ∩ A j) = μ ((E ∩ (A i)ᶜ) ∩ A j) := by
          rw [Measure.restrict_apply (hE.inter (hA j))]
          congr 1
          ext p
          simp only [mem_inter_iff]
          tauto
        simpa only [heq] using hfloor j hj'

/-- A common submeasure restores every floor in a finite collection, including
when labels from different families overlap. -/
theorem exists_common_floor_submeasure {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (w : ι → ℝ≥0∞) :
    ∃ ρ : Measure Ω, ρ ≤ μ ∧ μ univ ≤ ρ univ + ∑ i, w i ∧
      ∀ i, ρ (A i) = 0 ∨ w i ≤ ρ (A i) := by
  obtain ⟨E, hE, hmass, hfloor⟩ := simultaneous_floor_restriction A hA w Finset.univ μ
  refine ⟨μ.restrict E, Measure.restrict_le_self, ?_, ?_⟩
  · simpa only [Measure.restrict_apply_univ] using hmass
  · intro i
    rw [Measure.restrict_apply (hA i), inter_comm]
    exact hfloor i (Finset.mem_univ i)

end Submission.Lib.K4FullTimeLayers
