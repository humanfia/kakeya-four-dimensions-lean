import Mathlib

/-!
# Iterative pruning of light planks

A finite family of planks, each in one layer and one world, with measurable incidence
regions.  The *support* of a subfamily `S` in world `g` is the set of incidences lying,
for every layer, in some plank of `S` of that layer and world.  Repeatedly deleting
planks lighter than their floor, with respect to the measure restricted to the current
support, reaches a family all of whose planks are heavy; the support loses at most the
sum of the deleted floors.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return.Prune

open MeasureTheory Set

variable {ι W L α : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [MeasurableSpace α]

open Classical in
/-- In world `g`: for every layer, some plank of `S` of that layer and world. -/
def support (layer : ι → L) (world : ι → W) (region : ι → Set α) (S : Finset ι) (g : W) :
    Set α :=
  ⋂ ℓ : L, ⋃ i ∈ S.filter (fun i => layer i = ℓ ∧ world i = g), region i

omit [Fintype ι] [DecidableEq ι] [Fintype L] [MeasurableSpace α] in
theorem mem_support (layer : ι → L) (world : ι → W) (region : ι → Set α) (S : Finset ι)
    (g : W) (z : α) :
    z ∈ support layer world region S g ↔
      ∀ ℓ : L, ∃ i ∈ S, layer i = ℓ ∧ world i = g ∧ z ∈ region i := by
  classical
  simp only [support, Set.mem_iInter, Set.mem_iUnion, Finset.mem_filter, exists_prop]
  constructor
  · intro h ℓ
    obtain ⟨i, ⟨hiS, hℓ, hg⟩, hz⟩ := h ℓ
    exact ⟨i, hiS, hℓ, hg, hz⟩
  · intro h ℓ
    obtain ⟨i, hiS, hℓ, hg, hz⟩ := h ℓ
    exact ⟨i, ⟨hiS, hℓ, hg⟩, hz⟩

omit [Fintype ι] [Fintype L] in
/-- Deleting light planks loses at most their floors from the support. -/
theorem support_le_step [DecidableEq W] (layer : ι → L) (world : ι → W)
    (region : ι → Set α) (hregion : ∀ i, MeasurableSet (region i)) (ρ : W → Measure α)
    (thr : ι → ENNReal) (S S' : Finset ι)
    (hlight : ∀ i ∈ S, i ∉ S' →
      ((ρ (world i)).restrict (support layer world region S (world i))) (region i) < thr i)
    (g : W) :
    ρ g (support layer world region S g) ≤ ρ g (support layer world region S' g) +
      ∑ i ∈ (S \ S').filter (fun i => world i = g), thr i := by
  classical
  have hsub : support layer world region S g ⊆ support layer world region S' g ∪
      ⋃ i ∈ (S \ S').filter (fun i => world i = g),
        (support layer world region S g ∩ region i) := by
    intro z hz
    by_cases hz' : z ∈ support layer world region S' g
    · exact Or.inl hz'
    · right
      have hzS := (mem_support layer world region S g z).1 hz
      rw [mem_support] at hz'
      push Not at hz'
      obtain ⟨ℓ, hℓ⟩ := hz'
      obtain ⟨i, hiS, hiℓ, hig, hzi⟩ := hzS ℓ
      have hiS' : i ∉ S' := fun h => hℓ i h hiℓ hig hzi
      simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_sdiff, exists_prop]
      exact ⟨i, ⟨⟨hiS, hiS'⟩, hig⟩, hz, hzi⟩
  calc ρ g (support layer world region S g)
      ≤ ρ g (support layer world region S' g ∪
          ⋃ i ∈ (S \ S').filter (fun i => world i = g),
            (support layer world region S g ∩ region i)) := measure_mono hsub
    _ ≤ ρ g (support layer world region S' g) +
          ρ g (⋃ i ∈ (S \ S').filter (fun i => world i = g),
            (support layer world region S g ∩ region i)) := measure_union_le _ _
    _ ≤ ρ g (support layer world region S' g) +
          ∑ i ∈ (S \ S').filter (fun i => world i = g),
            ρ g (support layer world region S g ∩ region i) := by
        gcongr
        exact measure_biUnion_finset_le _ _
    _ ≤ ρ g (support layer world region S' g) +
          ∑ i ∈ (S \ S').filter (fun i => world i = g), thr i := by
        gcongr with i hi
        simp only [Finset.mem_filter, Finset.mem_sdiff] at hi
        have h := hlight i hi.1.1 hi.1.2
        rw [hi.2, Measure.restrict_apply (hregion i), Set.inter_comm] at h
        exact h.le

open Classical in
/-- One pruning step: keep the planks that are heavy on the current support. -/
noncomputable def pruneStep (layer : ι → L) (world : ι → W) (region : ι → Set α)
    (ρ : W → Measure α) (thr : ι → ENNReal) (S : Finset ι) : Finset ι :=
  S.filter (fun i =>
    thr i ≤ ((ρ (world i)).restrict (support layer world region S (world i))) (region i))

omit [Fintype ι] [DecidableEq ι] [Fintype L] in
theorem mem_pruneStep (layer : ι → L) (world : ι → W) (region : ι → Set α)
    (ρ : W → Measure α) (thr : ι → ENNReal) (S : Finset ι) (i : ι) :
    i ∈ pruneStep layer world region ρ thr S ↔
      i ∈ S ∧ thr i ≤
        ((ρ (world i)).restrict (support layer world region S (world i))) (region i) := by
  classical
  unfold pruneStep
  exact Finset.mem_filter

omit [Fintype ι] [DecidableEq ι] [Fintype L] in
theorem pruneStep_subset (layer : ι → L) (world : ι → W) (region : ι → Set α)
    (ρ : W → Measure α) (thr : ι → ENNReal) (S : Finset ι) :
    pruneStep layer world region ρ thr S ⊆ S := by
  intro i hi
  exact ((mem_pruneStep layer world region ρ thr S i).1 hi).1

theorem exists_pruned [DecidableEq W] (layer : ι → L) (world : ι → W) (region : ι → Set α)
    (hregion : ∀ i, MeasurableSet (region i)) (ρ : W → Measure α)
    [∀ g, IsFiniteMeasure (ρ g)] (thr : ι → ENNReal) :
    ∃ S : Finset ι,
      (∀ i ∈ S, thr i ≤
        ((ρ (world i)).restrict (support layer world region S (world i))) (region i)) ∧
      ∀ g, ρ g (support layer world region Finset.univ g) ≤
        ρ g (support layer world region S g) +
          ∑ i ∈ Finset.univ.filter (fun i => world i = g), thr i := by
  classical
  -- the invariant: the support has lost at most the floors of the deleted planks
  have hstep : ∀ S : Finset ι,
      (∀ g, ρ g (support layer world region Finset.univ g) ≤
        ρ g (support layer world region S g) +
          ∑ i ∈ (Finset.univ \ S).filter (fun i => world i = g), thr i) →
      ∀ g, ρ g (support layer world region Finset.univ g) ≤
        ρ g (support layer world region (pruneStep layer world region ρ thr S) g) +
          ∑ i ∈ (Finset.univ \ pruneStep layer world region ρ thr S).filter
            (fun i => world i = g), thr i := by
    intro S hS g
    set S' := pruneStep layer world region ρ thr S with hS'def
    have hS'S : S' ⊆ S := pruneStep_subset layer world region ρ thr S
    have hlight : ∀ i ∈ S, i ∉ S' →
        ((ρ (world i)).restrict (support layer world region S (world i))) (region i) <
          thr i := by
      intro i hi hni
      rw [hS'def, mem_pruneStep] at hni
      push Not at hni
      exact hni hi
    have h2 := support_le_step layer world region hregion ρ thr S S' hlight g
    have hsplit : ∑ i ∈ (Finset.univ \ S').filter (fun i => world i = g), thr i =
        ∑ i ∈ (Finset.univ \ S).filter (fun i => world i = g), thr i +
          ∑ i ∈ (S \ S').filter (fun i => world i = g), thr i := by
      rw [← Finset.sum_union]
      · congr 1
        ext i
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨hi, hg⟩
          by_cases hiS : i ∈ S
          · exact Or.inr ⟨⟨hiS, hi⟩, hg⟩
          · exact Or.inl ⟨hiS, hg⟩
        · rintro (⟨hiS, hg⟩ | ⟨⟨_, hi⟩, hg⟩)
          · exact ⟨fun h => hiS (hS'S h), hg⟩
          · exact ⟨hi, hg⟩
      · rw [Finset.disjoint_left]
        intro i hi hi'
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi hi'
        exact hi.1 hi'.1.1
    calc ρ g (support layer world region Finset.univ g)
        ≤ ρ g (support layer world region S g) +
          ∑ i ∈ (Finset.univ \ S).filter (fun i => world i = g), thr i := hS g
      _ ≤ (ρ g (support layer world region S' g) +
            ∑ i ∈ (S \ S').filter (fun i => world i = g), thr i) +
          ∑ i ∈ (Finset.univ \ S).filter (fun i => world i = g), thr i := by gcongr
      _ = ρ g (support layer world region S' g) +
            ∑ i ∈ (Finset.univ \ S').filter (fun i => world i = g), thr i := by
        rw [hsplit]; ring
  -- iterate until a fixed point, by induction on the cardinality
  have hfix : ∀ n : ℕ, ∀ S : Finset ι, S.card ≤ n →
      (∀ g, ρ g (support layer world region Finset.univ g) ≤
        ρ g (support layer world region S g) +
          ∑ i ∈ (Finset.univ \ S).filter (fun i => world i = g), thr i) →
      ∃ S' : Finset ι, pruneStep layer world region ρ thr S' = S' ∧
        ∀ g, ρ g (support layer world region Finset.univ g) ≤
          ρ g (support layer world region S' g) +
            ∑ i ∈ (Finset.univ \ S').filter (fun i => world i = g), thr i := by
    intro n
    induction n with
    | zero =>
      intro S hcard hS
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hS0
      refine ⟨∅, ?_, hS⟩
      exact Finset.subset_empty.mp (pruneStep_subset layer world region ρ thr ∅)
    | succ n ih =>
      intro S hcard hS
      by_cases hfS : pruneStep layer world region ρ thr S = S
      · exact ⟨S, hfS, hS⟩
      · have hss : pruneStep layer world region ρ thr S ⊂ S :=
          Finset.ssubset_iff_subset_ne.mpr ⟨pruneStep_subset layer world region ρ thr S, hfS⟩
        have hlt := Finset.card_lt_card hss
        exact ih _ (by omega) (hstep S hS)
  have hInvUniv : ∀ g, ρ g (support layer world region Finset.univ g) ≤
      ρ g (support layer world region Finset.univ g) +
        ∑ i ∈ (Finset.univ \ Finset.univ).filter (fun i => world i = g), thr i := by
    intro g
    exact le_self_add
  obtain ⟨S, hSf, hSInv⟩ := hfix _ Finset.univ le_rfl hInvUniv
  refine ⟨S, ?_, ?_⟩
  · intro i hi
    rw [← hSf] at hi
    exact ((mem_pruneStep layer world region ρ thr S i).1 hi).2
  · intro g
    calc ρ g (support layer world region Finset.univ g)
        ≤ ρ g (support layer world region S g) +
          ∑ i ∈ (Finset.univ \ S).filter (fun i => world i = g), thr i := hSInv g
      _ ≤ ρ g (support layer world region S g) +
          ∑ i ∈ Finset.univ.filter (fun i => world i = g), thr i := by
        gcongr
        exact Finset.sdiff_subset

end Submission.Obl.k4_scalar_candidate_original_return.Prune
