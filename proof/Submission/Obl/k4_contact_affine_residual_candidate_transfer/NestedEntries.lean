import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set
open scoped BigOperators

/-- A finite palette history records just the successive entry choices. -/
def EntryHistory (M : ℕ) : ℕ → Type
  | 0 => Fin M
  | h + 1 => EntryHistory M h × Fin M

scoped instance instFintypeEntryHistory (M h : ℕ) : Fintype (EntryHistory M h) := by
  induction h with
  | zero => exact inferInstanceAs (Fintype (Fin M))
  | succ h ih =>
    letI := ih
    exact inferInstanceAs (Fintype (EntryHistory M h × Fin M))

theorem card_entryHistory (M h : ℕ) : Fintype.card (EntryHistory M h) = M ^ (h + 1) := by
  induction h with
  | zero =>
    change Fintype.card (Fin M) = M ^ (0 + 1)
    rw [Fintype.card_fin, pow_one]
  | succ h ih =>
    change Fintype.card (EntryHistory M h × Fin M) = M ^ (h + 1 + 1)
    rw [Fintype.card_prod, ih, Fintype.card_fin]
    simp only [pow_succ]

/-- Refine the original trajectory assignments by the actual entry choices
along their fixed ancestor chain. -/
def historyAssignment {α : Type*} {M : ℕ} (n : ℕ → ℕ)
    (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h)) :
    (h : ℕ) → Fin (n h) → EntryHistory M h → Set α
  | 0, i, u => A 0 i ∩ entry 0 i u
  | h + 1, i, u =>
    (A (h + 1) i ∩ historyAssignment n A entry parent h (parent h i) u.1) ∩
      entry (h + 1) i u.2

theorem historyAssignment_subset {α : Type*} {M : ℕ} (n : ℕ → ℕ)
    (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h))
    (h : ℕ) (i : Fin (n h)) (u : EntryHistory M h) :
    historyAssignment n A entry parent h i u ⊆ A h i := by
  cases h
  · exact inter_subset_left
  · exact inter_subset_left.trans inter_subset_left

theorem historyAssignment_subset_parent {α : Type*} {M : ℕ} (n : ℕ → ℕ)
    (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h))
    (h : ℕ) (i : Fin (n (h + 1))) (u : EntryHistory M h) (v : Fin M) :
    historyAssignment n A entry parent (h + 1) i (u, v) ⊆
      historyAssignment n A entry parent h (parent h i) u :=
  inter_subset_left.trans inter_subset_right

theorem measurableSet_historyAssignment {α : Type*} [MeasurableSpace α] {M : ℕ}
    (n : ℕ → ℕ) (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h))
    (hA : ∀ h i, MeasurableSet (A h i))
    (hentry : ∀ h i u, MeasurableSet (entry h i u))
    (h : ℕ) (i : Fin (n h)) (u : EntryHistory M h) :
    MeasurableSet (historyAssignment n A entry parent h i u) := by
  induction h with
  | zero => exact (hA 0 i).inter (hentry 0 i u)
  | succ h ih => exact ((hA _ i).inter (ih (parent h i) u.1)).inter (hentry _ i u.2)

theorem disjoint_historyAssignment {α : Type*} {M : ℕ} (n : ℕ → ℕ)
    (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h))
    (hentry : ∀ h i, Pairwise (fun u v => Disjoint (entry h i u) (entry h i v)))
    (h : ℕ) (i : Fin (n h)) : Pairwise (fun u v =>
      Disjoint (historyAssignment n A entry parent h i u)
        (historyAssignment n A entry parent h i v)) := by
  induction h with
  | zero =>
    intro u v huv
    exact (hentry 0 i huv).mono inter_subset_right inter_subset_right
  | succ h ih =>
    intro u v huv
    by_cases hlast : u.2 = v.2
    · have hprefix : u.1 ≠ v.1 := fun hp => huv (Prod.ext hp hlast)
      exact (ih (parent h i) hprefix).mono
        (inter_subset_left.trans inter_subset_right) (inter_subset_left.trans inter_subset_right)
    · exact (hentry _ i hlast).mono inter_subset_right inter_subset_right

/-- Histories retain the original label disjointness within each time block. -/
theorem disjoint_labeled_historyAssignment {α J : Type*} {M : ℕ} (n : ℕ → ℕ)
    (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h))
    (hentry : ∀ h i, Pairwise (fun u v => Disjoint (entry h i u) (entry h i v)))
    (h : ℕ) (j : Fin (n h) → J)
    (hA : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A h i) (A h i'))
    (a b : Fin (n h) × EntryHistory M h) (hab : a ≠ b) (hj : j a.1 = j b.1) :
    Disjoint (historyAssignment n A entry parent h a.1 a.2)
      (historyAssignment n A entry parent h b.1 b.2) := by
  by_cases hi : a.1 = b.1
  · have hu : a.2 ≠ b.2 := fun heq => hab (Prod.ext hi heq)
    rw [← hi]
    exact disjoint_historyAssignment n A entry parent hentry h a.1 hu
  · exact (hA a.1 b.1 hi hj).mono (historyAssignment_subset n A entry parent h _ _)
      (historyAssignment_subset n A entry parent h _ _)

/-- Appending histories charges each original reference only the number of
actual entry histories. There is no additional count of time blocks. -/
theorem sum_history_references {R : Type*} [AddCommMonoid R] {n M h : ℕ}
    (w : Fin n → R) :
    (∑ a : Fin n × EntryHistory M h, w a.1) = M ^ (h + 1) • ∑ i, w i := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, card_entryHistory, Finset.sum_nsmul]

/-- Simultaneous successful entries on an actual ancestor chain give one
history assignment. No new choice of time blocks is introduced. -/
theorem exists_historyAssignment {α : Type*} {M : ℕ} (n : ℕ → ℕ)
    (A : (h : ℕ) → Fin (n h) → Set α)
    (entry : (h : ℕ) → Fin (n h) → Fin M → Set α)
    (parent : (h : ℕ) → Fin (n (h + 1)) → Fin (n h))
    (path : (h : ℕ) → Fin (n h)) (hpath : ∀ h, parent h (path (h + 1)) = path h)
    (l : α) (m : ℕ) (hA : ∀ h ≤ m, l ∈ A h (path h))
    (hentry : ∀ h ≤ m, ∃ u, l ∈ entry h (path h) u) :
    ∃ u, l ∈ historyAssignment n A entry parent m (path m) u := by
  induction m with
  | zero =>
    obtain ⟨u, hu⟩ := hentry 0 le_rfl
    exact ⟨u, hA 0 le_rfl, hu⟩
  | succ m ih =>
    obtain ⟨u, hu⟩ := ih (fun h hh => hA h (Nat.le_succ_of_le hh))
      (fun h hh => hentry h (Nat.le_succ_of_le hh))
    obtain ⟨v, hv⟩ := hentry (m + 1) le_rfl
    refine ⟨(u, v), ⟨hA (m + 1) le_rfl, ?_⟩, hv⟩
    simpa only [hpath m] using hu

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
