import Submission.Lib.K4OriginalLists

/-!
Adapted from: here:o064

Measurable finite maximization and analytical list rules.  Only finitely many
pairwise score comparisons enter the choice, so arbitrary real-valued weights
produce measurable membership events, including at ties.
-/

namespace Submission.Lib.K4MeshListRecovery

open Finset MeasureTheory Set
open Submission.Lib.K4OriginalLists

/-- Finite measurable scores admit a measurable maximizing choice. -/
theorem exists_measurable_finite_argmax
    {X α : Type*} [MeasurableSpace X] [Fintype α] [Nonempty α]
    (score : α → X → ℝ) (hscore : ∀ a, Measurable (score a)) :
    ∃ select : X → α, (∀ a, MeasurableSet {x | select x = a}) ∧
      ∀ x a, score a x ≤ score (select x) x := by
  classical
  let comparison : X → (α × α → Bool) :=
    fun x c => decide (score c.1 x ≤ score c.2 x)
  let pick : (α × α → Bool) → α := fun P =>
    if h : ∃ a, ∀ b, P (b, a) = true then Classical.choose h else Classical.choice inferInstance
  have hcomparison : Measurable comparison := by
    apply Measurable.of_eval
    intro c
    apply measurable_to_bool
    simpa only [comparison, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
      measurableSet_le (hscore c.1) (hscore c.2)
  have hnonempty (x : X) : ∃ a, ∀ b, comparison x (b, a) = true := by
    obtain ⟨a, _, hmax⟩ := (univ : Finset α).exists_max_image (fun a => score a x) univ_nonempty
    exact ⟨a, fun b => by simpa only [comparison, decide_eq_true_eq] using hmax b (mem_univ b)⟩
  let : MeasurableSpace α := ⊤
  have hselect : Measurable (fun x => pick (comparison x)) :=
    (measurable_of_countable pick).comp hcomparison
  refine ⟨fun x => pick (comparison x), ?_, ?_⟩
  · intro a
    have ha : MeasurableSet ({a} : Set α) := by trivial
    simpa only [Set.preimage, Set.mem_singleton_iff] using ha.preimage hselect
  · intro x a
    have hgood : ∀ b, comparison x (b, pick (comparison x)) = true := by
      dsimp [pick]
      rw [dite_eq_left (hnonempty x)]
      exact Classical.choose_spec (hnonempty x)
    simpa only [comparison, decide_eq_true_eq] using hgood a

/-- Bounded-cardinality maximizing list policies can be chosen measurably, even at ties. -/
theorem exists_measurable_maximizing_lists
    {X β : Type*} [MeasurableSpace X] [Fintype β]
    (allowed : Finset β) (D : ℕ) (w : X → β → ℝ)
    (hw : ∀ a, Measurable (fun x => w x a)) :
    ∃ L : X → Finset β, MeasurableLists L ∧
      (∀ x, L x ⊆ allowed ∧ (L x).card ≤ D) ∧
      ∀ x (T : Finset β), T ⊆ allowed → T.card ≤ D →
        (∑ a ∈ T, w x a) ≤ ∑ a ∈ L x, w x a := by
  classical
  let candidates := allowed.powerset.filter (fun s => s.card ≤ D)
  have hempty : (∅ : Finset β) ∈ candidates := by simp [candidates]
  have : Nonempty candidates := ⟨⟨∅, hempty⟩⟩
  have hscores (s : candidates) : Measurable (fun x => ∑ a ∈ s.val, w x a) := by fun_prop
  obtain ⟨select, hselect, hmax⟩ := exists_measurable_finite_argmax
    (fun s : candidates => fun x => ∑ a ∈ s.val, w x a) hscores
  refine ⟨fun x => (select x).val, ?_, ?_, ?_⟩
  · intro a
    have hU := (univ.filter (fun s : candidates => a ∈ s.val)).measurableSet_biUnion
      (fun s _ => hselect s)
    convert hU using 1
    ext x
    simp
  · intro x
    simpa only [candidates, mem_filter, Finset.mem_powerset] using (select x).property
  · intro x T hT hcard
    exact hmax x ⟨T, by simp [candidates, hT, hcard]⟩

end Submission.Lib.K4MeshListRecovery
