import Mathlib

set_option autoImplicit false

/-!
# Selecting one option per fiber of an integer index, by measure

"Select one polynomial pair per fiber by averaging" (paper, Section 8, common coefficient field),
for a measure instead of finitely many weighted states: if every point of `U` agrees with one of
the at most `n` options of its fiber `idx p`, choosing on each fiber the option of largest agreeing
mass keeps at least `1/n` of the mass of `U`.
-/

namespace Submission.Obl.k4_conditional_common_affine_field

open MeasureTheory

/-- Decomposition of a set along the fibers of an integer index with values in a finite set. -/
theorem measure_eq_sum_fibers {X : Type*} [MeasurableSpace X] (μ : Measure X) (U : Set X)
    (hU : MeasurableSet U) (idx : X → ℤ) (hidx : Measurable idx) (Rg : Finset ℤ)
    (hRg : ∀ p ∈ U, idx p ∈ Rg) :
    μ U = ∑ j ∈ Rg, μ (U ∩ idx ⁻¹' {j}) := by
  have hU' : U = ⋃ j ∈ Rg, U ∩ idx ⁻¹' {j} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hp; exact ⟨idx p, hRg p hp, hp, rfl⟩
    · rintro ⟨j, _, hp, _⟩; exact hp
  conv_lhs => rw [hU']
  rw [measure_biUnion_finset]
  · intro i _ j _ hij
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      ((Set.disjoint_singleton.mpr hij).preimage idx)
  · intro j _; exact hU.inter (hidx (measurableSet_singleton j))

/-- **Selection by measure.** Every point of `U` agrees (`Ag a`) with some option `a` of the at most
`n` options of its fiber; choosing the heaviest option on each fiber keeps `μ U / n`. -/
theorem exists_measure_selection {X β : Type*} [MeasurableSpace X] [Inhabited β]
    (μ : Measure X) (U : Set X) (hU : MeasurableSet U) (idx : X → ℤ) (hidx : Measurable idx)
    (Rg : Finset ℤ) (hRg : ∀ p ∈ U, idx p ∈ Rg) (opts : ℤ → Finset β) {n : ℕ}
    (hn : ∀ j, (opts j).card ≤ n) (Ag : β → Set X) (hAg : ∀ a, MeasurableSet (Ag a))
    (hcover : ∀ p ∈ U, ∃ a ∈ opts (idx p), p ∈ Ag a) :
    ∃ sel : ℤ → β, (∀ p ∈ U, sel (idx p) ∈ opts (idx p)) ∧
      MeasurableSet {p | p ∈ Ag (sel (idx p))} ∧
      μ U ≤ n * μ (U ∩ {p | p ∈ Ag (sel (idx p))}) := by
  classical
  have hsel : ∀ j, ∃ a : β, (opts j).Nonempty → a ∈ opts j ∧
      ∀ a' ∈ opts j, μ (U ∩ idx ⁻¹' {j} ∩ Ag a') ≤ μ (U ∩ idx ⁻¹' {j} ∩ Ag a) := by
    intro j
    by_cases hne : (opts j).Nonempty
    · obtain ⟨a, ha, hmax⟩ :=
        Finset.exists_max_image (opts j) (fun a => μ (U ∩ idx ⁻¹' {j} ∩ Ag a)) hne
      exact ⟨a, fun _ => ⟨ha, hmax⟩⟩
    · exact ⟨default, fun h => absurd h hne⟩
  choose sel hsel using hsel
  have hSelMeas : MeasurableSet {p | p ∈ Ag (sel (idx p))} := by
    have : {p | p ∈ Ag (sel (idx p))} = ⋃ j : ℤ, idx ⁻¹' {j} ∩ Ag (sel j) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨idx p, rfl, h⟩
      · rintro ⟨j, rfl, h⟩; exact h
    rw [this]
    exact MeasurableSet.iUnion fun j => (hidx (measurableSet_singleton j)).inter (hAg _)
  refine ⟨sel, ?_, hSelMeas, ?_⟩
  · intro p hp
    obtain ⟨a, ha, _⟩ := hcover p hp
    exact (hsel (idx p) ⟨a, ha⟩).1
  · rw [measure_eq_sum_fibers μ U hU idx hidx Rg hRg,
      measure_eq_sum_fibers μ (U ∩ {p | p ∈ Ag (sel (idx p))}) (hU.inter hSelMeas) idx hidx Rg
        (fun p hp => hRg p hp.1), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hne : (opts j).Nonempty
    · obtain ⟨_, hmax⟩ := hsel j hne
      have hsub : U ∩ idx ⁻¹' {j} ⊆ ⋃ a ∈ opts j, U ∩ idx ⁻¹' {j} ∩ Ag a := by
        intro p hp
        obtain ⟨a, ha, hpa⟩ := hcover p hp.1
        have hj : idx p = j := hp.2
        rw [hj] at ha
        exact Set.mem_biUnion ha ⟨hp, hpa⟩
      calc μ (U ∩ idx ⁻¹' {j}) ≤ μ (⋃ a ∈ opts j, U ∩ idx ⁻¹' {j} ∩ Ag a) := measure_mono hsub
        _ ≤ ∑ a ∈ opts j, μ (U ∩ idx ⁻¹' {j} ∩ Ag a) := measure_biUnion_finset_le _ _
        _ ≤ ∑ _a ∈ opts j, μ (U ∩ idx ⁻¹' {j} ∩ Ag (sel j)) :=
            Finset.sum_le_sum fun a ha => hmax a ha
        _ = (opts j).card * μ (U ∩ idx ⁻¹' {j} ∩ Ag (sel j)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ n * μ (U ∩ idx ⁻¹' {j} ∩ Ag (sel j)) := by
            gcongr; exact_mod_cast hn j
        _ = n * μ (U ∩ {p | p ∈ Ag (sel (idx p))} ∩ idx ⁻¹' {j}) := by
            congr 2
            ext p
            simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
              Set.mem_ofPred_eq]
            constructor
            · rintro ⟨⟨hU, hj⟩, ha⟩; exact ⟨⟨hU, by rw [hj]; exact ha⟩, hj⟩
            · rintro ⟨⟨hU, ha⟩, hj⟩; exact ⟨⟨hU, hj⟩, by rw [← hj]; exact ha⟩
    · have : U ∩ idx ⁻¹' {j} = ∅ := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hp hj
        obtain ⟨a, ha, _⟩ := hcover p hp
        rw [hj] at ha
        exact hne ⟨a, ha⟩
      rw [this, measure_empty]; exact zero_le

end Submission.Obl.k4_conditional_common_affine_field
