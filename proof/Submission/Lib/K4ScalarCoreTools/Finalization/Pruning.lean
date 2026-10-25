/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/Pruning.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Uniform finite-subfamily bound: accepted here:o130, k4_scalar_initial_true_horizon/FiniteCardBound.lean.
Original unnormalized pruning: o062/x0212, Recovery.lean as retained at4d8af73c.
-/

import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MeasureTheory
open scoped ENNReal

theorem finite_of_uniform_finset_card_bound {ι : Type*} (S : Set ι) (C : ℝ)
    (hcount : ∀ F : Finset ι, (↑F : Set ι) ⊆ S → (F.card : ℝ) ≤ C) : S.Finite := by
  classical
  by_contra hinf
  have hInf : S.Infinite := hinf
  obtain ⟨n, hn⟩ := exists_nat_gt C
  obtain ⟨F, hFS, hcard⟩ := hInf.exists_subset_card_eq n
  have hbound := hcount F hFS
  rw [hcard] at hbound
  exact (not_le_of_gt hn) hbound

theorem prune_small_labels {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    (I : Finset ι) (A : ι → Set X) (R : ι → ℝ≥0∞) {τ B : ℝ≥0∞}
    (hR : ∑ i ∈ I, R i ≤ B) :
    ∃ F : Finset ι, F ⊆ I ∧ (∀ i ∈ F, τ * R i ≤ μ (A i)) ∧
      μ (⋃ i ∈ I, A i) ≤ μ (⋃ i ∈ F, A i) + τ * B := by
  classical
  let F := I.filter (fun i => τ * R i ≤ μ (A i))
  have hF : F ⊆ I := Finset.filter_subset _ _
  have hbad : μ (⋃ i ∈ I \ F, A i) ≤ τ * B := by
    calc
      μ (⋃ i ∈ I \ F, A i) ≤ ∑ i ∈ I \ F, μ (A i) :=
        measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ I \ F, τ * R i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_sdiff.mp hi
        have hn : ¬ τ * R i ≤ μ (A i) := by
          intro h
          exact hi'.2 (Finset.mem_filter.mpr ⟨hi'.1, h⟩)
        exact (lt_of_not_ge hn).le
      _ = τ * ∑ i ∈ I \ F, R i := by rw [Finset.mul_sum]
      _ ≤ τ * ∑ i ∈ I, R i := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset (f := R)
          (Finset.sdiff_subset : I \ F ⊆ I)) (show 0 ≤ τ from bot_le)
      _ ≤ τ * B := mul_le_mul_of_nonneg_left hR (show 0 ≤ τ from bot_le)
  have hcover : (⋃ i ∈ I, A i) ⊆ (⋃ i ∈ F, A i) ∪ (⋃ i ∈ I \ F, A i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    by_cases hif : i ∈ F
    · exact Or.inl (mem_iUnion₂.mpr ⟨i, hif, hxi⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hif⟩, hxi⟩)
  refine ⟨F, hF, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add le_rfl hbad))

end Submission.Lib.K4ScalarCoreTools.Finalization
