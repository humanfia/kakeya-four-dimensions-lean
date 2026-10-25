-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.MeasurableLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/MeasurableLists.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/MeasurableLists.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/MeasurableLists.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/MeasurableLists.lean.
   Original comments and attributions are preserved below. -/
import Mathlib

/-! Finite analytic prediction families allow measurable lists with the same
pointwise cardinal bound. The initially supplied lists may be arbitrary. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set

private theorem analytic_inter {X : Type*} [TopologicalSpace X] [T2Space X]
    {s t : Set X} (hs : AnalyticSet s) (ht : AnalyticSet t) : AnalyticSet (s ∩ t) := by
  have h : ∀ b : Bool, AnalyticSet (if b then s else t) := by
    intro b
    cases b <;> assumption
  have heq : (⋂ b : Bool, if b then s else t) = s ∩ t := by
    ext x
    constructor
    · intro hx
      exact ⟨mem_iInter.mp hx true, mem_iInter.mp hx false⟩
    · rintro ⟨hxs, hxt⟩
      apply mem_iInter.mpr
      intro b
      cases b <;> assumption
  simpa only [heq] using AnalyticSet.iInter h

private theorem analytic_finset_inter {X I : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (J : Finset I) (s : I → Set X)
    (hs : ∀ i ∈ J, AnalyticSet (s i)) : AnalyticSet {x | ∀ i ∈ J, x ∈ s i} := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using (MeasurableSet.univ : MeasurableSet (univ : Set X)).analyticSet
  | @insert a J ha ih =>
    have heq : {x | ∀ i ∈ insert a J, x ∈ s i} = s a ∩ {x | ∀ i ∈ J, x ∈ s i} := by
      ext x
      simp
    rw [heq]
    exact analytic_inter (hs a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)))

/-- A finite family of analytic sets with empty intersection has measurable
supersets whose intersection is still empty. -/
theorem analytic_empty_inter_enlargement {X I : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (J : Finset I) (s : I → Set X) (hs : ∀ i ∈ J, AnalyticSet (s i))
    (hempty : ∀ x, ¬ ∀ i ∈ J, x ∈ s i) :
    ∃ U : I → Set X, (∀ i, MeasurableSet (U i)) ∧
      (∀ i ∈ J, s i ⊆ U i) ∧ ∀ x, ¬ ∀ i ∈ J, x ∈ U i := by
  classical
  induction J using Finset.induction_on generalizing s with
  | empty =>
    refine ⟨fun _ => univ, fun _ => MeasurableSet.univ, by simp, ?_⟩
    intro x _
    exact hempty x (by simp)
  | @insert a J ha ih =>
    by_cases hJ : J = ∅
    · subst J
      refine ⟨fun i => if i = a then ∅ else univ, ?_, ?_, ?_⟩
      · intro i
        dsimp only
        split <;> simp
      · intro i hi x hx
        have hi : i = a := by simpa using hi
        subst i
        exact False.elim (hempty x (by simpa using hx))
      · intro x hx
        simpa using hx a (Finset.mem_insert_self _ _)
    · let t : Set X := {x | ∀ i ∈ J, x ∈ s i}
      have ht : AnalyticSet t := analytic_finset_inter J s
        (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      have hd : Disjoint (s a) t := disjoint_left.mpr (by
        intro x hxa hxt
        exact hempty x (by simpa [t] using And.intro hxa hxt))
      obtain ⟨U, hsU, htU, hU⟩ := (hs a (Finset.mem_insert_self _ _)).measurablySeparable ht hd
      let s' : I → Set X := fun i => s i ∩ U
      have hs' : ∀ i ∈ J, AnalyticSet (s' i) := fun i hi =>
        analytic_inter (hs i (Finset.mem_insert_of_mem hi)) hU.analyticSet
      have he' : ∀ x, ¬ ∀ i ∈ J, x ∈ s' i := by
        intro x hx
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hJ
        have hxU : x ∈ U := (hx i hi).2
        exact (disjoint_left.mp htU) (fun j hj => (hx j hj).1) hxU
      obtain ⟨V, hV, hsV, heV⟩ := ih s' hs' he'
      refine ⟨fun i => if i = a then U else V i ∪ Uᶜ, ?_, ?_, ?_⟩
      · intro i
        dsimp only
        split
        · exact hU
        · exact (hV i).union hU.compl
      · intro i hi x hx
        by_cases hia : i = a
        · subst i
          simpa using hsU hx
        · simp only [ite_eq_right hia, mem_union, mem_compl_iff]
          by_cases hxU : x ∈ U
          · exact Or.inl (hsV i ((Finset.mem_insert.mp hi).resolve_left hia) ⟨hx, hxU⟩)
          · exact Or.inr hxU
      · intro x hx
        have hxU : x ∈ U := by simpa using hx a (Finset.mem_insert_self _ _)
        apply heV x
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        have hx' := hx i (Finset.mem_insert_of_mem hi)
        simpa only [ite_eq_right hia, mem_union, mem_compl_iff, hxU, not_true_eq_false,
          or_false] using hx'

/-- Measurability of an initial finite prediction list is unnecessary when
each predicted event is analytic. A measurable replacement keeps the same cap. -/
theorem analytic_prediction_list {X I : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [Fintype I] (s : I → Set X) (hs : ∀ i, AnalyticSet (s i))
    (L : X → Finset I) (D : ℝ) (hcard : ∀ x, ((L x).card : ℝ) ≤ D)
    (hpred : ∀ i x, x ∈ s i → i ∈ L x) :
    ∃ L' : X → Finset I, (∀ i, MeasurableSet {x | i ∈ L' x}) ∧
      (∀ x, ((L' x).card : ℝ) ≤ D) ∧ ∀ i x, x ∈ s i → i ∈ L' x := by
  classical
  have hsep (J : Finset I) : ∃ U : I → Set X, (∀ i, MeasurableSet (U i)) ∧
      (∀ i, s i ⊆ U i) ∧ (D < (J.card : ℝ) → ∀ x, ¬ ∀ i ∈ J, x ∈ U i) := by
    by_cases hbad : D < (J.card : ℝ)
    · have he : ∀ x, ¬ ∀ i ∈ J, x ∈ s i := by
        intro x hx
        have hsub : J ⊆ L x := fun i hi => hpred i x (hx i hi)
        have hc : (J.card : ℝ) ≤ (L x).card := by exact_mod_cast Finset.card_le_card hsub
        exact (not_lt_of_ge (hc.trans (hcard x))) hbad
      obtain ⟨U, hU, hsU, heU⟩ := analytic_empty_inter_enlargement J s (fun i _ => hs i) he
      refine ⟨fun i => if i ∈ J then U i else univ, ?_, ?_, ?_⟩
      · intro i
        dsimp only
        split
        · exact hU i
        · exact MeasurableSet.univ
      · intro i
        dsimp only
        split
        · exact hsU i ‹i ∈ J›
        · exact subset_univ _
      · intro _ x hx
        exact heU x (fun i hi => by simpa only [ite_eq_left hi] using hx i hi)
    · exact ⟨fun _ => univ, fun _ => MeasurableSet.univ,
        fun _ => subset_univ _, fun h => False.elim (hbad h)⟩
  choose U hU hsU heU using hsep
  let B : I → Set X := fun i => ⋂ J : Finset I, U J i
  have hB (i : I) : MeasurableSet (B i) := MeasurableSet.iInter (fun J => hU J i)
  let L' : X → Finset I := fun x => Finset.univ.filter (fun i => x ∈ B i)
  refine ⟨L', ?_, ?_, ?_⟩
  · intro i
    simpa only [L', Finset.mem_filter, Finset.mem_univ, true_and, ofPred_mem_eq] using hB i
  · intro x
    by_contra! hbad
    apply heU (L' x) hbad x
    intro i hi
    have hxi : x ∈ B i := (Finset.mem_filter.mp hi).2
    exact mem_iInter.mp hxi (L' x)
  · intro i x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, mem_iInter.mpr ?_⟩
    intro J
    exact hsU J i hx

/-- For a standard Borel incidence space, every finite family of measurable
events predicted by an arbitrary bounded observation list has a measurable
prediction list with the identical bound. -/
theorem measurable_event_prediction_list {Ω X I : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [Fintype I] (obs : Ω → X) (hobs : Measurable obs)
    (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (L : X → Finset I) (D : ℝ) (hcard : ∀ x, ((L x).card : ℝ) ≤ D)
    (hpred : ∀ i p, p ∈ E i → i ∈ L (obs p)) :
    ∃ L' : X → Finset I, (∀ i, MeasurableSet {x | i ∈ L' x}) ∧
      (∀ x, ((L' x).card : ℝ) ≤ D) ∧ ∀ i p, p ∈ E i → i ∈ L' (obs p) := by
  obtain ⟨L', hL', hc, hp⟩ := analytic_prediction_list (fun i => obs '' E i)
    (fun i => (hE i).analyticSet_image hobs) L D hcard
    (fun i x hx => by
      obtain ⟨p, hp, rfl⟩ := hx
      exact hpred i p hp)
  exact ⟨L', hL', hc, fun i p hpE => hp i (obs p) ⟨p, hpE, rfl⟩⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
