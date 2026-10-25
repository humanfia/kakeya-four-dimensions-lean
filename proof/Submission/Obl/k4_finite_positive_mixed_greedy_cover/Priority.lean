import Submission.Obl.k4_quadratic_finite_greedy_cover.PrioritySets

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set
open Submission.Obl.k4_quadratic_finite_greedy_cover
open scoped ENNReal

/-- Priority selection for an arbitrary mixture of geometric envelopes. The
certificate supplied by discovery is retained without changing its original law. -/
theorem mixed_priority_selection {X α β κ : Type*} [MeasurableSpace X]
    [Fintype β] [Fintype κ] [DecidableEq α]
    (ν : κ → Measure X) (ω : κ → ℝ) (H : κ → Set (X × ℝ))
    (A : β → Set X) (γ : β → κ) (parent : α → β)
    (piece envelope : α → Set X) (I : α → Set ℝ) (Good : α → Prop)
    {θ : ℝ} (hθ : 0 < θ)
    (hApos : ∀ b, 0 < (ν (γ b)).real (A b))
    (hAfin : ∀ b, ν (γ b) (A b) ≠ ∞)
    (hHm : ∀ w, MeasurableSet (H w))
    (hHfin : ∀ w, (ν w).prod volume (H w) ≠ ∞)
    (hGood : ∀ a, Good a → MeasurableSet (piece a) ∧ piece a ⊆ A (parent a) ∧
      MeasurableSet (I a) ∧
      θ ≤ (ν (γ (parent a))).real (piece a) / (ν (γ (parent a))).real (A (parent a)))
    (hselect : ∀ S : Finset α, (∀ a ∈ S, Good a) →
      ∀ R : κ → Set (X × ℝ), (∀ w, MeasurableSet (R w) ∧ R w ⊆ H w) →
      (∑ w, ω w * ((ν w).prod volume).real (H w)) / 2 ≤
        ∑ w, ω w * ((ν w).prod volume).real (R w) →
      (∀ w, R w = H w \ selectedUnion S (fun a => γ (parent a))
        (fun a => piece a ×ˢ I a) w) →
      ∃ a, Good a ∧ piece a = envelope a \ selectedUnion S parent piece (parent a)) :
    ∃ S : Finset α,
      (∀ a ∈ S, Good a) ∧
      (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → parent a = parent a' → Disjoint (piece a) (piece a')) ∧
      (∀ a ∈ S, ∃ P : Finset α, P ⊆ S ∧
        piece a = envelope a \ selectedUnion P parent envelope (parent a)) ∧
      (S.card : ℝ) ≤ (Fintype.card β : ℝ) / θ ∧
      (∑ w, ω w * ((ν w).prod volume).real (H w)) / 2 ≤
        ∑ w, ω w * ((ν w).prod volume).real
          (H w ∩ selectedUnion S (fun a => γ (parent a)) (fun a => piece a ×ˢ I a) w) := by
  classical
  let P : Finset α → Prop := fun S =>
    (∀ a ∈ S, Good a) ∧
    (∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → parent a = parent a' → Disjoint (piece a) (piece a')) ∧
    (∀ b, selectedUnion S parent piece b = selectedUnion S parent envelope b) ∧
    ∀ a ∈ S, ∃ P' : Finset α, P' ⊆ S ∧
      piece a = envelope a \ selectedUnion P' parent envelope (parent a)
  let Stop : Finset α → Prop := fun S =>
    (∑ w, ω w * ((ν w).prod volume).real (H w)) / 2 ≤
      ∑ w, ω w * ((ν w).prod volume).real
        (H w ∩ selectedUnion S (fun a => γ (parent a)) (fun a => piece a ×ˢ I a) w)
  let weight : α → ℝ := fun a =>
    (ν (γ (parent a))).real (piece a) / (ν (γ (parent a))).real (A (parent a))
  have hbudget (S : Finset α) (hs : P S) : (∑ a ∈ S, weight a) ≤ (Fintype.card β : ℝ) :=
    normalized_assignment_budget (fun b => ν (γ b)) A parent piece hApos hAfin S
      (fun a ha => ⟨(hGood a (hs.1 a ha)).1, (hGood a (hs.1 a ha)).2.1⟩) hs.2.1
  have hstep (S : Finset α) (hs : P S) (hnstop : ¬ Stop S) :
      False ∨ ∃ a, a ∉ S ∧ P (insert a S) ∧ θ ≤ weight a := by
    let Cov := selectedUnion S (fun a => γ (parent a)) (fun a => piece a ×ˢ I a)
    let R := fun w => H w \ Cov w
    have hCovm (w : κ) : MeasurableSet (Cov w) :=
      selectedUnion_measurable S _ _
        (fun a ha => (hGood a (hs.1 a ha)).1.prod (hGood a (hs.1 a ha)).2.2.1) w
    have hRm (w : κ) : MeasurableSet (R w) := (hHm w).diff (hCovm w)
    have hbalance : (∑ w, ω w * ((ν w).prod volume).real (R w)) +
        (∑ w, ω w * ((ν w).prod volume).real (H w ∩ Cov w)) =
        ∑ w, ω w * ((ν w).prod volume).real (H w) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      rw [← mul_add]
      congr 1
      exact measureReal_sdiff_add_inter (μ := (ν w).prod volume) (s := H w) (hCovm w) (hHfin w)
    have hRmass : (∑ w, ω w * ((ν w).prod volume).real (H w)) / 2 ≤
        ∑ w, ω w * ((ν w).prod volume).real (R w) := by
      dsimp [Stop] at hnstop
      linarith [lt_of_not_ge hnstop]
    obtain ⟨a, ha, hnew⟩ := hselect S hs.1 R (fun w => ⟨hRm w, sdiff_subset⟩) hRmass (fun _ => rfl)
    have hinc : θ ≤ weight a := (hGood a ha).2.2.2
    have hfresh : a ∉ S := by
      intro has
      have hempty : piece a = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro l hl
        have hn := (hnew ▸ hl).2
        exact hn (mem_iUnion₂.mpr ⟨a, has, rfl, hl⟩)
      have hz : weight a = 0 := by simp [weight, hempty]
      rw [hz] at hinc
      linarith
    refine Or.inr ⟨a, hfresh, ⟨?_, priority_disjoint_insert S parent piece envelope a hs.2.1 hnew,
      priority_union_insert S parent piece envelope a hs.2.2.1 hnew, ?_⟩, hinc⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ha
      · exact hs.1 b hb
    · intro b hb
      rcases Finset.mem_insert.mp hb with hba | hb
      · subst b
        refine ⟨S, Finset.subset_insert _ _, ?_⟩
        rw [← hs.2.2.1 (parent a)]
        exact hnew
      · obtain ⟨P', hP', hrep⟩ := hs.2.2.2 b hb
        exact ⟨P', hP'.trans (Finset.subset_insert _ _), hrep⟩
  obtain ⟨S, hS, hstop⟩ := (finite_selection_or_exit weight P Stop False hθ
    (by simp [P, selectedUnion]) hbudget hstep).resolve_left id
  refine ⟨S, hS.1, hS.2.1, hS.2.2.2, ?_, hstop⟩
  apply (le_div_iff₀ hθ).mpr
  calc
    (S.card : ℝ) * θ = ∑ _a ∈ S, θ := by simp
    _ ≤ ∑ a ∈ S, weight a := Finset.sum_le_sum (fun a ha => (hGood a (hS.1 a ha)).2.2.2)
    _ ≤ _ := hbudget S hS

end Submission.Obl.k4_finite_positive_mixed_greedy_cover
