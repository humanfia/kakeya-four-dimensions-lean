-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.MergeBasics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, MergeBasics.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory

/-- Join all pieces with a common new prism label. -/
def mergePieces {Ω : Type*} {n L K : ℕ} (f : Fin L → Fin K)
    (W : Fin n → Fin L → Set Ω) (i : Fin n) (k : Fin K) : Set Ω :=
  ⋃ j ∈ {j | f j = k}, W i j

theorem mem_mergePieces {Ω : Type*} {n L K : ℕ} (f : Fin L → Fin K)
    (W : Fin n → Fin L → Set Ω) (i : Fin n) (k : Fin K) (p : Ω) :
    p ∈ mergePieces f W i k ↔ ∃ j, f j = k ∧ p ∈ W i j := by
  simp [mergePieces]

theorem mergePieces_measurable {Ω : Type*} [MeasurableSpace Ω] {n L K : ℕ}
    (f : Fin L → Fin K) (W : Fin n → Fin L → Set Ω)
    (hW : ∀ i j, MeasurableSet (W i j)) (i : Fin n) (k : Fin K) :
    MeasurableSet (mergePieces f W i k) := by
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hW i j

theorem mergePieces_disjoint {Ω : Type*} {n L K : ℕ} (f : Fin L → Fin K)
    (W : Fin n → Fin L → Set Ω)
    (hW : ∀ i j j', j ≠ j' → Disjoint (W i j) (W i j'))
    (i : Fin n) (k k' : Fin K) (hkk : k ≠ k') :
    Disjoint (mergePieces f W i k) (mergePieces f W i k') := by
  apply Set.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨j, hj, hp⟩ := (mem_mergePieces f W i k p).mp hp
  obtain ⟨j', hj', hp'⟩ := (mem_mergePieces f W i k' p).mp hp'
  have hne : j ≠ j' := by
    intro he
    subst j'
    exact hkk (hj.symm.trans hj')
  exact Set.disjoint_left.mp (hW i j j' hne) hp hp'

theorem mergePieces_measure {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    {n L K : ℕ} (f : Fin L → Fin K) (W : Fin n → Fin L → Set Ω)
    (hWm : ∀ i j, MeasurableSet (W i j))
    (hW : ∀ i j j', j ≠ j' → Disjoint (W i j) (W i j'))
    (i : Fin n) (k : Fin K) :
    ν (mergePieces f W i k) = ∑ j, if f j = k then ν (W i j) else 0 := by
  classical
  have he : mergePieces f W i k = ⋃ j, if f j = k then W i j else ∅ := by
    ext p
    simp only [mem_mergePieces, mem_iUnion]
    constructor
    · rintro ⟨j, hj, hp⟩
      exact ⟨j, by simpa only [ite_eq_left hj] using hp⟩
    · rintro ⟨j, hp⟩
      by_cases hj : f j = k
      · exact ⟨j, hj, by simpa only [ite_eq_left hj] using hp⟩
      · simp only [ite_eq_right hj, mem_empty_iff_false] at hp
  rw [he, measure_iUnion, tsum_fintype]
  · apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  · intro j j' hne
    dsimp only [Function.onFun]
    split_ifs <;> first | exact hW i j j' hne | simp
  · intro j
    split_ifs
    · exact hWm i j
    · exact MeasurableSet.empty

theorem mergePieces_total_measure {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    {n L K : ℕ} (f : Fin L → Fin K) (W : Fin n → Fin L → Set Ω)
    (hWm : ∀ i j, MeasurableSet (W i j))
    (hW : ∀ i j j', j ≠ j' → Disjoint (W i j) (W i j')) :
    ∑ i, ∑ k, ν (mergePieces f W i k) = ∑ i, ∑ j, ν (W i j) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mergePieces_measure ν f W hWm hW i]
  rw [Finset.sum_comm]
  simp

/-- A fine tube cannot occur in two old labels at the same point. Thus
cardinalities of all angular tests add exactly under merging. -/
theorem mergePieces_ncard {Ω : Type*} {n L K : ℕ} (f : Fin L → Fin K)
    (W : Fin n → Fin L → Set Ω)
    (hW : ∀ i j j', j ≠ j' → Disjoint (W i j) (W i j'))
    (p : Ω) (k : Fin K) (R : Fin n → Prop) :
    {i | p ∈ mergePieces f W i k ∧ R i}.ncard =
      ∑ j, if f j = k then {i | p ∈ W i j ∧ R i}.ncard else 0 := by
  classical
  let S : Fin L → Set (Fin n) := fun j => if f j = k then {i | p ∈ W i j ∧ R i} else ∅
  have he : {i | p ∈ mergePieces f W i k ∧ R i} = ⋃ j, S j := by
    ext i
    simp only [mem_ofPred_eq, mem_mergePieces, mem_iUnion]
    constructor
    · rintro ⟨⟨j, hj, hp⟩, hR⟩
      exact ⟨j, by simpa only [S, ite_eq_left hj, mem_ofPred_eq] using And.intro hp hR⟩
    · rintro ⟨j, hi⟩
      by_cases hj : f j = k
      · simp only [S, ite_eq_left hj, mem_ofPred_eq] at hi
        exact ⟨⟨j, hj, hi.1⟩, hi.2⟩
      · simp only [S, ite_eq_right hj, mem_empty_iff_false] at hi
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro j j' hne
    apply Set.disjoint_left.mpr
    intro i hi hi'
    by_cases hj : f j = k
    · by_cases hj' : f j' = k
      · simp only [S, ite_eq_left hj, ite_eq_left hj', mem_ofPred_eq] at hi hi'
        exact Set.disjoint_left.mp (hW i j j' hne) hi.1 hi'.1
      · simp only [S, ite_eq_right hj', mem_empty_iff_false] at hi'
    · simp only [S, ite_eq_right hj, mem_empty_iff_false] at hi
  rw [he, Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _) hd,
    finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [S]
  split_ifs <;> simp

theorem mergePieces_count_bound {Ω : Type*} {n L K : ℕ} (f : Fin L → Fin K)
    (W : Fin n → Fin L → Set Ω)
    (hW : ∀ i j j', j ≠ j' → Disjoint (W i j) (W i j'))
    (p : Ω) (k : Fin K) (R : Fin n → Prop) {C : ℝ}
    (hbound : ∀ j, ({i | p ∈ W i j ∧ R i}.ncard : ℝ) ≤
      C * ({i | p ∈ W i j}.ncard : ℝ)) :
    ({i | p ∈ mergePieces f W i k ∧ R i}.ncard : ℝ) ≤
      C * ({i | p ∈ mergePieces f W i k}.ncard : ℝ) := by
  classical
  have hfull := mergePieces_ncard f W hW p k (fun _ => True)
  simp only [and_true] at hfull
  rw [mergePieces_ncard f W hW p k R, hfull]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact hbound j
  · simp

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
