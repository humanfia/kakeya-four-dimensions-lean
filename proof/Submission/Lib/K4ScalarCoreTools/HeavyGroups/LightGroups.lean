/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups/LightGroups.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit af6b1867dfbb677a4a0e008effa5b557d8531e7f,
Submission/Obl/k4_scalar_mesh_projection/LightGroups.lean.
-/

import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Set MeasureTheory

/-- Removing light groups loses at most their common threshold times the
original group count. Every retained floor refers to the original law. -/
theorem retain_heavy_original_groups {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (G : Finset I) (E : I → Set Ω)
    (q N : ℝ) (hq : 0 ≤ q) (hcount : (G.card : ℝ) ≤ N)
    (hE : ∀ i ∈ G, MeasurableSet (E i)) :
    ∃ H : Finset I, H ⊆ G ∧ (∀ i ∈ H, q ≤ (μ (E i)).toReal) ∧
      MeasurableSet (⋃ i ∈ H, E i) ∧
      μ (⋃ i ∈ G, E i) ≤ μ (⋃ i ∈ H, E i) + ENNReal.ofReal (q * N) := by
  classical
  let H := G.filter fun i => q ≤ (μ (E i)).toReal
  have hHG : H ⊆ G := Finset.filter_subset _ _
  have hheavy : ∀ i ∈ H, q ≤ (μ (E i)).toReal := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hcover : (⋃ i ∈ G, E i) ⊆ (⋃ i ∈ H, E i) ∪ (⋃ i ∈ G \ H, E i) := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_union] at hx ⊢
    obtain ⟨i, hi, hx⟩ := hx
    by_cases hiH : i ∈ H
    · exact Or.inl ⟨i, hiH, hx⟩
    · exact Or.inr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hiH⟩, hx⟩
  have hlight (i : I) (hi : i ∈ G \ H) : μ (E i) ≤ ENNReal.ofReal q := by
    have hnot : ¬ q ≤ (μ (E i)).toReal := by
      intro h
      exact (Finset.mem_sdiff.mp hi).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, h⟩)
    calc
      μ (E i) = ENNReal.ofReal ((μ (E i)).toReal) := (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge hnot))
  have hcard0 : ((G \ H).card : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : G \ H ⊆ G))
  have hcard : ((G \ H).card : ℝ) ≤ N := hcard0.trans hcount
  have hloss : μ (⋃ i ∈ G \ H, E i) ≤ ENNReal.ofReal (q * N) := by
    calc
      _ ≤ ∑ i ∈ G \ H, μ (E i) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ G \ H, ENNReal.ofReal q := Finset.sum_le_sum hlight
      _ = ENNReal.ofReal (∑ _i ∈ G \ H, q) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i hi => hq)).symm
      _ = ENNReal.ofReal (q * ((G \ H).card : ℝ)) := by simp [mul_comm]
      _ ≤ ENNReal.ofReal (q * N) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcard hq)
  refine ⟨H, hHG, hheavy, ?_, ?_⟩
  · exact H.measurableSet_biUnion fun i hi => hE i (hHG hi)
  · calc
      _ ≤ μ ((⋃ i ∈ H, E i) ∪ (⋃ i ∈ G \ H, E i)) := measure_mono hcover
      _ ≤ μ (⋃ i ∈ H, E i) + μ (⋃ i ∈ G \ H, E i) := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl hloss

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
