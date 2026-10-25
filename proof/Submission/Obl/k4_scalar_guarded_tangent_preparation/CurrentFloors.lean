import Mathlib

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

/-- Repeatedly delete a currently light packet. Each packet is charged
at most once to its fixed original-prior budget. The resulting law is
one measurable restriction, and every surviving packet has its current
mass floor simultaneously. -/
theorem exists_current_floor_mask
    {Ω ι : Type*} [MeasurableSpace Ω] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (cost : ι → ℝ≥0∞)
    (s : Finset ι) (μ : Measure Ω) :
    ∃ G : Set Ω, MeasurableSet G ∧
      μ univ ≤ (μ.restrict G) univ + ∑ i ∈ s, cost i ∧
      ∀ i ∈ s, (μ.restrict G) (E i) = 0 ∨ cost i ≤ (μ.restrict G) (E i) := by
  classical
  revert μ
  refine Finset.strongInductionOn s ?_
  intro s ih μ
  by_cases hgood : ∀ i ∈ s, μ (E i) = 0 ∨ cost i ≤ μ (E i)
  · refine ⟨univ, MeasurableSet.univ, ?_, ?_⟩
    · simp only [Measure.restrict_univ]
      exact le_self_add
    · simpa only [Measure.restrict_univ] using hgood
  · push Not at hgood
    obtain ⟨i, hi, hnonzero, hlight⟩ := hgood
    let μ₁ := μ.restrict (E i)ᶜ
    obtain ⟨G₁, hG₁, hmass, hfloors⟩ :=
      ih (s.erase i) (Finset.erase_ssubset hi) μ₁
    let G := G₁ ∩ (E i)ᶜ
    have hG : MeasurableSet G := hG₁.inter (hE i).compl
    have heq : μ.restrict G = μ₁.restrict G₁ := by
      dsimp only [G, μ₁]
      rw [Measure.restrict_restrict hG₁]
    have hzero : (μ.restrict G) (E i) = 0 := by
      rw [Measure.restrict_apply (hE i)]
      have hempty : E i ∩ G = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hx.2.2 hx.1
      rw [hempty, measure_empty]
    refine ⟨G, hG, ?_, ?_⟩
    · have hsplit : μ univ = μ (E i) + μ₁ univ := by
        dsimp only [μ₁]
        rw [Measure.restrict_apply_univ]
        exact (measure_add_measure_compl (μ := μ) (hE i)).symm
      have hsum : (∑ j ∈ s.erase i, cost j) + cost i = ∑ j ∈ s, cost j :=
        Finset.sum_erase_add s cost hi
      calc
        μ univ = μ (E i) + μ₁ univ := hsplit
        _ ≤ cost i + μ₁ univ := add_le_add hlight.le le_rfl
        _ ≤ cost i + ((μ₁.restrict G₁) univ + ∑ j ∈ s.erase i, cost j) :=
          add_le_add le_rfl hmass
        _ = (μ.restrict G) univ + ∑ j ∈ s, cost j := by
          rw [heq, ← hsum]
          ac_rfl
    · intro j hj
      by_cases hji : j = i
      · subst j
        exact Or.inl hzero
      · rw [heq]
        exact hfloors j (Finset.mem_erase.mpr ⟨hji, hj⟩)
/-- Removing entries whose current rectangle mass is zero preserves
coverage by their original earlier witness sets. -/
theorem support_after_zero_packet_pruning
    {Ω ι : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (C E : ι → Set Ω) (s : Finset ι) (hCE : ∀ i ∈ s, C i ⊆ E i)
    (hcover : ν (⋃ i ∈ s, C i)ᶜ = 0) :
    ν (⋃ i ∈ s.filter (fun i => ν (E i) ≠ 0), C i)ᶜ = 0 := by
  classical
  let zeroed := s.filter (fun i => ν (E i) = 0)
  have hzeroed : ν (⋃ i ∈ zeroed, E i) = 0 := by
    apply le_antisymm ?_ bot_le
    apply (measure_biUnion_finset_le zeroed E).trans
    apply le_of_eq
    exact Finset.sum_eq_zero (fun i hi => (Finset.mem_filter.mp hi).2)
  have hsub : (⋃ i ∈ s.filter (fun i => ν (E i) ≠ 0), C i)ᶜ ⊆
      (⋃ i ∈ s, C i)ᶜ ∪ (⋃ i ∈ zeroed, E i) := by
    intro x hx
    by_cases hold : x ∈ ⋃ i ∈ s, C i
    · obtain ⟨i, hi, hCi⟩ := Set.mem_iUnion₂.mp hold
      by_cases hzero : ν (E i) = 0
      · exact Or.inr (Set.mem_iUnion₂.mpr
          ⟨i, Finset.mem_filter.mpr ⟨hi, hzero⟩, hCE i hi hCi⟩)
      · exact False.elim (hx (Set.mem_iUnion₂.mpr
          ⟨i, Finset.mem_filter.mpr ⟨hi, hzero⟩, hCi⟩))
    · exact Or.inl hold
  exact measure_mono_null hsub (measure_union_null hcover hzeroed)

end Submission.Obl.k4_scalar_guarded_tangent_preparation
