import Mathlib

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Set

noncomputable section

lemma analytic_inter {X : Type*} [TopologicalSpace X] [T2Space X]
    {A B : Set X} (hA : AnalyticSet A) (hB : AnalyticSet B) : AnalyticSet (A ∩ B) := by
  have heq : A ∩ B = ⋂ b : Bool, if b then A else B := by
    ext x
    constructor
    · rintro ⟨hxA, hxB⟩
      exact mem_iInter.mpr (fun b => by cases b <;> assumption)
    · intro hx
      exact ⟨mem_iInter.mp hx true, mem_iInter.mp hx false⟩
  rw [heq]
  exact AnalyticSet.iInter (fun b => by cases b; exact hB; exact hA)

/-- Finite families of analytic sets with empty common intersection have
measurable supersets with empty common intersection. -/
theorem analytic_empty_inter_supersets {X : Type*} [TopologicalSpace X] [T2Space X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] :
    ∀ (n : ℕ) (S : Fin n → Set X), (∀ i, AnalyticSet (S i)) → (⋂ i, S i) = ∅ →
      ∃ T : Fin n → Set X, (∀ i, MeasurableSet (T i) ∧ S i ⊆ T i) ∧ (⋂ i, T i) = ∅ := by
  intro n
  induction n with
  | zero =>
    intro S hS hzero
    refine ⟨S, fun i => Fin.elim0 i, hzero⟩
  | succ n ih =>
    intro S hS hzero
    by_cases hn : n = 0
    · subst n
      have hS0 : S 0 = ∅ := by
        rw [← hzero]
        ext x
        constructor
        · intro hx
          refine mem_iInter.mpr (fun i => ?_)
          have hi : i = 0 := Fin.ext (by omega)
          simpa only [hi] using hx
        · exact fun hx => mem_iInter.mp hx 0
      refine ⟨S, ?_, hzero⟩
      intro i
      have hi : i = 0 := Fin.ext (by omega)
      refine ⟨?_, Subset.rfl⟩
      rw [hi, hS0]
      exact MeasurableSet.empty
    have hnpos : 0 < n := by omega
    letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    let A := ⋂ i : Fin n, S i.castSucc
    have hA : AnalyticSet A := AnalyticSet.iInter (fun i => hS i.castSucc)
    have hdis : Disjoint A (S (Fin.last n)) := by
      rw [Set.disjoint_left]
      intro x hxA hxB
      have hx : x ∈ ⋂ i, S i := mem_iInter.mpr
        (Fin.lastCases hxB (fun i => mem_iInter.mp hxA i))
      rw [hzero] at hx
      exact hx
    obtain ⟨U, hAU, hBU, hU⟩ := hA.measurablySeparable (hS (Fin.last n)) hdis
    let C : Fin n → Set X := fun i => S i.castSucc ∩ Uᶜ
    have hC : ∀ i, AnalyticSet (C i) := fun i =>
      analytic_inter (hS i.castSucc) hU.compl.analyticSet
    have hCzero : (⋂ i, C i) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxA : x ∈ A := mem_iInter.mpr (fun i => (mem_iInter.mp hx i).1)
      exact (mem_iInter.mp hx ⟨0, hnpos⟩).2 (hAU hxA)
    obtain ⟨V, hV, hVzero⟩ := ih C hC hCzero
    let T : Fin (n + 1) → Set X := Fin.lastCases Uᶜ (fun i => V i ∪ U)
    refine ⟨T, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa only [T, Fin.lastCases_last] using
          And.intro hU.compl (show S (Fin.last n) ⊆ Uᶜ from
            fun x hx hxU => Set.disjoint_left.mp hBU hx hxU)
      · intro i
        simp only [T, Fin.lastCases_castSucc]
        refine ⟨(hV i).1.union hU, ?_⟩
        intro x hx
        by_cases hxU : x ∈ U
        · exact Or.inr hxU
        · exact Or.inl ((hV i).2 ⟨hx, hxU⟩)
    · apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxU : x ∉ U := by
        have hz := mem_iInter.mp hx (Fin.last n)
        change x ∈ Uᶜ
        simpa only [T, Fin.lastCases_last] using hz
      have hxV : x ∈ ⋂ i, V i := mem_iInter.mpr (fun i => by
        have hz := mem_iInter.mp hx i.castSucc
        simp only [T, Fin.lastCases_castSucc, mem_union] at hz
        exact hz.resolve_right hxU)
      rw [hVzero] at hxV
      exact hxV

/-- A finite family of analytic supports can be enlarged to measurable
supports while retaining any pointwise multiplicity bound. -/
theorem analytic_measurable_lists {X I : Type*} [TopologicalSpace X] [T2Space X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype I] [LinearOrder I]
    (S : I → Set X) (hS : ∀ i, AnalyticSet (S i)) (K : ℝ)
    (L : X → Finset I) (hL : ∀ x, ((L x).card : ℝ) ≤ K)
    (hsupp : ∀ i x, x ∈ S i → i ∈ L x) :
    ∃ Λ : X → Finset I, (∀ i, MeasurableSet {x | i ∈ Λ x}) ∧
      (∀ x, ((Λ x).card : ℝ) ≤ K) ∧ (∀ i x, x ∈ S i → i ∈ Λ x) := by
  classical
  have hfinite (J : Finset I) (hJ : K < (J.card : ℝ)) :
      (⋂ i : Fin J.card, S ((J.orderIsoOfFin rfl i).val)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hsub : J ⊆ L x := by
      intro i hi
      let z : J := ⟨i, hi⟩
      have hz := mem_iInter.mp hx ((J.orderIsoOfFin rfl).symm z)
      simp only [OrderIso.apply_symm_apply] at hz
      exact hsupp i x hz
    have hc : (J.card : ℝ) ≤ ((L x).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    linarith [hL x]
  choose T hT hTzero using (fun J : {J : Finset I // K < (J.card : ℝ)} =>
    analytic_empty_inter_supersets J.val.card
      (fun i => S ((J.val.orderIsoOfFin rfl i).val))
      (fun i => hS _) (hfinite J.val J.property))
  let U : I → Set X := fun i => ⋂ J : {J : Finset I // K < (J.card : ℝ)},
    ⋂ z : {z : Fin J.val.card // (J.val.orderIsoOfFin rfl z).val = i}, T J z.val
  have hU : ∀ i, MeasurableSet (U i) := fun i =>
    MeasurableSet.iInter (fun J => MeasurableSet.iInter (fun z => (hT J z.val).1))
  have hSU : ∀ i, S i ⊆ U i := by
    intro i x hx
    refine mem_iInter.mpr (fun J => mem_iInter.mpr (fun z => ?_))
    apply (hT J z.val).2
    simpa only [z.property] using hx
  let Λ : X → Finset I := fun x => Finset.univ.filter (fun i => x ∈ U i)
  refine ⟨Λ, ?_, ?_, ?_⟩
  · intro i
    have heq : {x | i ∈ Λ x} = U i := by
      ext x
      simp only [Λ, mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    exact hU i
  · intro x
    by_contra hbad
    have hxJ : K < ((Λ x).card : ℝ) := lt_of_not_ge hbad
    let J : {J : Finset I // K < (J.card : ℝ)} := ⟨Λ x, hxJ⟩
    have hxT : x ∈ ⋂ z : Fin J.val.card, T J z := by
      refine mem_iInter.mpr (fun z => ?_)
      have hz : (J.val.orderIsoOfFin rfl z).val ∈ Λ x := (J.val.orderIsoOfFin rfl z).property
      have hxU : x ∈ U (J.val.orderIsoOfFin rfl z).val := (Finset.mem_filter.mp hz).2
      exact mem_iInter.mp (mem_iInter.mp hxU J) ⟨z, rfl⟩
    rw [hTzero J] at hxT
    exact hxT
  · intro i x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hSU i hx⟩

end
end Submission.Obl.k4_raw_critical_segment_forests
