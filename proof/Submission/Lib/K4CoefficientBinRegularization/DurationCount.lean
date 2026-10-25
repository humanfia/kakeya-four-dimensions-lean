-- Adapted from: here:o202 (session x0952), Regularization/DurationCount.lean.
import Submission.Lib.K4IncidenceWitnesses

namespace Submission.Lib.K4CoefficientBinRegularization.Reg

open MeasureTheory Set
open scoped ENNReal Classical

/-- Counting finitely many long time witnesses by their maximum multiplicity. -/
theorem finite_count_of_duration {ι : Type*} [DecidableEq ι]
    (C : Finset ι) (E : ι → Set ℝ) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hE : ∀ i ∈ C, MeasurableSet (E i))
    (hunit : ∀ i ∈ C, E i ⊆ Icc (0 : ℝ) 1)
    (hlong : ∀ i ∈ C, ENNReal.ofReal δ ≤ volume (E i))
    (hcount : ∀ t : ℝ, ((C.filter fun i => t ∈ E i).card : ℝ) ≤ M) :
    (C.card : ℝ) * δ ≤ M := by
  classical
  have hsum : (C.card : ℝ≥0∞) * ENNReal.ofReal δ ≤ ENNReal.ofReal M := by
    calc
      _ = ∑ _i ∈ C, ENNReal.ofReal δ := by simp
      _ ≤ ∑ i ∈ C, volume (E i) := Finset.sum_le_sum hlong
      _ = ∫⁻ t, ∑ i ∈ C, (E i).indicator (1 : ℝ → ℝ≥0∞) t := by
        rw [lintegral_finsetSum C (fun i hi => measurable_one.indicator (hE i hi))]
        exact Finset.sum_congr rfl fun i hi => (lintegral_indicator_one (hE i hi)).symm
      _ ≤ ∫⁻ t, (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal M) t := by
        apply lintegral_mono
        intro t
        by_cases ht : t ∈ Icc (0 : ℝ) 1
        · rw [indicator_of_mem ht]
          have heq : ∑ i ∈ C, (E i).indicator (1 : ℝ → ℝ≥0∞) t =
              ((C.filter fun i => t ∈ E i).card : ℝ≥0∞) := by
            rw [Finset.card_filter]
            push_cast
            apply Finset.sum_congr rfl
            intro i hi
            by_cases h : t ∈ E i
            · simp only [indicator_of_mem h, Pi.one_apply, if_pos h]
            · simp only [indicator_of_notMem h, if_neg h]
          change (∑ i ∈ C, (E i).indicator (1 : ℝ → ℝ≥0∞) t) ≤ _
          rw [heq, ← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (hcount t)
        · rw [indicator_of_notMem ht]
          have hz : ∀ i ∈ C, (E i).indicator (1 : ℝ → ℝ≥0∞) t = 0 := by
            intro i hi
            exact indicator_of_notMem (fun h => ht (hunit i hi h)) _
          simp only [Finset.sum_eq_zero hz, le_refl]
      _ = ENNReal.ofReal M := by
        rw [lintegral_indicator_const measurableSet_Icc]
        simp
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hsum
  exact (ENNReal.ofReal_le_ofReal_iff hM).mp hsum

end Submission.Lib.K4CoefficientBinRegularization.Reg
