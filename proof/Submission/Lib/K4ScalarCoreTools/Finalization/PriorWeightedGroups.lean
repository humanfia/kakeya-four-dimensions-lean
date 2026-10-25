/-
Adapted from: here:o062
Original proof: x0511/b4b965c9c9fe730b6f4bf9fec6c2e3c97843e419, PriorWeightedGroups.lean.
Original reference pruning is imported from the internal Pruning module.
-/

import Submission.Lib.K4ScalarCoreTools.Finalization.Pruning

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MeasureTheory
open scoped ENNReal BigOperators

/-- Original-prior-weighted pruning supplies the duration bound needed by
the physical cell count, without first assuming a bound on the group count. -/
theorem prune_groups_with_original_prior_budget {X I : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (μ : Measure (X × ℝ)) [IsFiniteMeasure μ]
    (G : Finset I) (A : I → Set X) (B : Set ℝ)
    (hA : ∀ i ∈ G, MeasurableSet (A i))
    (hdisj : Set.PairwiseDisjoint (↑G : Set I) A)
    (h K : ℝ) (hh : 0 < h) (hK : 0 < K) :
    ∃ H : Finset I, H ⊆ G ∧
      (∀ i ∈ H, ν (A i) ≤ ENNReal.ofReal (K / h) * μ (A i ×ˢ B) ∧
        (ν (A i)).toReal ≤ K * (μ (A i ×ˢ B)).toReal / h) ∧
      μ (⋃ i ∈ G, A i ×ˢ B) ≤ μ (⋃ i ∈ H, A i ×ˢ B) +
        ENNReal.ofReal (h / K) * ν univ := by
  have hbudget : (∑ i ∈ G, ν (A i)) ≤ ν univ := by
    rw [← measure_biUnion_finset hdisj hA]
    exact measure_mono (subset_univ _)
  let E : I → Set (X × ℝ) := fun i => A i ×ˢ B
  obtain ⟨H, hHG, hfloor, hloss⟩ := prune_small_labels μ G E (fun i => ν (A i))
    (τ := ENNReal.ofReal (h / K)) (B := ν univ) hbudget
  have hcancel : ENNReal.ofReal (K / h) * ENNReal.ofReal (h / K) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ K / h)]
    have hid : K / h * (h / K) = 1 := by field_simp [hh.ne', hK.ne']
    rw [hid]
    simp
  have hcap (i : I) (hi : i ∈ H) :
      ν (A i) ≤ ENNReal.ofReal (K / h) * μ (A i ×ˢ B) := by
    have hb := mul_le_mul' (le_refl (ENNReal.ofReal (K / h))) (hfloor i hi)
    simpa only [← mul_assoc, hcancel, one_mul] using hb
  refine ⟨H, hHG, ?_, ?_⟩
  · intro i hi
    refine ⟨hcap i hi, ?_⟩
    have hr := ENNReal.toReal_mono (by finiteness) (hcap i hi)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ K / h),
      div_mul_eq_mul_div] using hr
  · simpa only [E] using hloss

end Submission.Lib.K4ScalarCoreTools.Finalization
