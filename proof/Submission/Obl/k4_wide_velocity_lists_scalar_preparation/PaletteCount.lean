import Mathlib

/-!
# Palette double counting of occupied output states

If every occupied output state has its velocity bins dominated by `C` times a
palette of total mass at most one, and every event lies in the velocity-wise
list of its own bin, then at most `C * M` states are occupied, where `M` bounds
every list. This is the integration of the velocity-wise counts against the
original palette (paper, proof of Proposition 8.4, "Scalar support after
subtraction").
-/

namespace Submission.Obl.k4_wide_velocity_lists_scalar_preparation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Every occupied state sees compatible palette mass at least `C⁻¹`; summing
over states and exchanging the sums gives the count. -/
theorem occupied_card_le {Ω O : Type*} [MeasurableSpace Ω]
    (τ : Measure Ω) [IsFiniteMeasure τ] (out : Ω → O) (vel : Ω → ℤ)
    (πv : ℤ → ℝ≥0∞) (hπ : ∑' a, πv a ≤ 1)
    (L : ℤ → Finset O) (M : ℝ≥0∞) (hL : ∀ a, ((L a).card : ℝ≥0∞) ≤ M)
    (hmem : ∀ᵐ p ∂τ, out p ∈ L (vel p)) (C : ℝ≥0∞)
    (hdom : ∀ o a, τ {p | out p = o ∧ vel p = a} ≤ C * πv a * τ {p | out p = o})
    (S : Finset O) (hS : ∀ o ∈ S, τ {p | out p = o} ≠ 0) :
    (S.card : ℝ≥0∞) ≤ C * M := by
  classical
  have hnull : τ {p | out p ∉ L (vel p)} = 0 := by
    exact ae_iff.mp hmem
  have hone : ∀ o ∈ S, 1 ≤ C * ∑' a, (if o ∈ L a then πv a else 0) := by
    intro o ho
    have hpos := hS o ho
    have hfin : τ {p | out p = o} ≠ ⊤ := measure_ne_top τ _
    have hsplit : τ {p | out p = o} ≤ ∑' a, τ {p | out p = o ∧ vel p = a} := by
      calc τ {p | out p = o} = τ (⋃ a, {p | out p = o ∧ vel p = a}) := by
            congr 1; ext p; simp
        _ ≤ _ := measure_iUnion_le _
    have hterm : ∀ a, τ {p | out p = o ∧ vel p = a} ≤
        (if o ∈ L a then πv a else 0) * (C * τ {p | out p = o}) := by
      intro a
      split_ifs with hoa
      · calc _ ≤ C * πv a * τ {p | out p = o} := hdom o a
          _ = _ := by ring
      · rw [zero_mul]
        calc τ {p | out p = o ∧ vel p = a} ≤ τ {p | out p ∉ L (vel p)} := by
              apply measure_mono
              rintro p ⟨hpo, hpa⟩
              simp only [mem_ofPred_eq, hpo, hpa]
              exact hoa
          _ = 0 := hnull
    have hle : 1 * τ {p | out p = o} ≤
        (C * ∑' a, (if o ∈ L a then πv a else 0)) * τ {p | out p = o} := by
      calc 1 * τ {p | out p = o} = τ {p | out p = o} := one_mul _
        _ ≤ ∑' a, τ {p | out p = o ∧ vel p = a} := hsplit
        _ ≤ ∑' a, (if o ∈ L a then πv a else 0) * (C * τ {p | out p = o}) :=
          ENNReal.tsum_le_tsum hterm
        _ = (∑' a, (if o ∈ L a then πv a else 0)) * (C * τ {p | out p = o}) :=
          ENNReal.tsum_mul_right
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_left hpos hfin).mp hle
  calc (S.card : ℝ≥0∞) = ∑ o ∈ S, (1 : ℝ≥0∞) := by simp
    _ ≤ ∑ o ∈ S, C * ∑' a, (if o ∈ L a then πv a else 0) := Finset.sum_le_sum hone
    _ = C * ∑' a, ∑ o ∈ S, (if o ∈ L a then πv a else 0) := by
      rw [← Finset.mul_sum, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = C * ∑' a, ((S.filter (fun o => o ∈ L a)).card : ℝ≥0∞) * πv a := by
      congr 1
      apply tsum_congr
      intro a
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * ∑' a, M * πv a := by
      gcongr with a
      calc ((S.filter (fun o => o ∈ L a)).card : ℝ≥0∞) ≤ ((L a).card : ℝ≥0∞) := by
            exact_mod_cast Finset.card_le_card (fun o ho => (Finset.mem_filter.mp ho).2)
        _ ≤ M := hL a
    _ = C * (M * ∑' a, πv a) := by rw [ENNReal.tsum_mul_left]
    _ ≤ C * (M * 1) := by gcongr
    _ = C * M := by rw [mul_one]

/-- The occupied states form a finite list of at most `C * M` members, which
carries the whole law. -/
theorem exists_terminal_of_palette {Ω O : Type*} [MeasurableSpace Ω] [Countable O]
    (τ : Measure Ω) [IsFiniteMeasure τ] (out : Ω → O) (vel : Ω → ℤ)
    (πv : ℤ → ℝ≥0∞) (hπ : ∑' a, πv a ≤ 1)
    (L : ℤ → Finset O) (M : ℝ≥0∞) (hL : ∀ a, ((L a).card : ℝ≥0∞) ≤ M)
    (hmem : ∀ᵐ p ∂τ, out p ∈ L (vel p)) (C : ℝ≥0∞) (hCM : C * M ≠ ⊤)
    (hdom : ∀ o a, τ {p | out p = o ∧ vel p = a} ≤ C * πv a * τ {p | out p = o}) :
    ∃ terminal : Finset O, (terminal.card : ℝ≥0∞) ≤ C * M ∧
      ∀ᵐ p ∂τ, out p ∈ terminal := by
  classical
  have hfin : {o | τ {p | out p = o} ≠ 0}.Finite := by
    by_contra hinf
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hCM
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have h := occupied_card_le τ out vel πv hπ L M hL hmem C hdom t (fun o ho => ht ho)
    rw [htc] at h
    exact absurd h (not_le.mpr hn)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · exact occupied_card_le τ out vel πv hπ L M hL hmem C hdom hfin.toFinset
      (fun o ho => hfin.mem_toFinset.mp ho)
  · rw [ae_iff]
    have hsub : {p | ¬ out p ∈ hfin.toFinset} ⊆
        ⋃ o : O, {p | out p = o ∧ τ {p | out p = o} = 0} := by
      intro p hp
      simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, not_not] at hp
      exact mem_iUnion.mpr ⟨out p, rfl, hp⟩
    apply measure_mono_null hsub
    apply measure_iUnion_null
    intro o
    by_cases ho : τ {p | out p = o} = 0
    · exact measure_mono_null (fun p hp => hp.1) ho
    · have : {p | out p = o ∧ τ {p | out p = o} = 0} = ∅ := by
        ext p; simp [ho]
      rw [this, measure_empty]

end

end Submission.Obl.k4_wide_velocity_lists_scalar_preparation
