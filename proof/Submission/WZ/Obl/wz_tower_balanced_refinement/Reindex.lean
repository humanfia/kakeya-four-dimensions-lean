-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_balanced_refinement.Reindex.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_balanced_refinement

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Enumerate a selected finite set without repetitions. -/
def enumerate {α : Type*} (S : Finset α) : Fin S.card → α :=
  fun i => ((Finset.equivFin S).symm i).val

lemma enumerate_mem {α : Type*} (S : Finset α) (i : Fin S.card) : enumerate S i ∈ S :=
  ((Finset.equivFin S).symm i).property

lemma enumerate_injective {α : Type*} (S : Finset α) : Function.Injective (enumerate S) :=
  Subtype.val_injective.comp (Finset.equivFin S).symm.injective

lemma exists_enumerate {α : Type*} (S : Finset α) {a : α} (ha : a ∈ S) :
    ∃ i, enumerate S i = a := by
  refine ⟨Finset.equivFin S ⟨a, ha⟩, ?_⟩
  simp [enumerate]

lemma sum_enumerate {α A : Type*} [AddCommMonoid A] (S : Finset α) (w : α → A) :
    ∑ i : Fin S.card, w (enumerate S i) = ∑ a ∈ S, w a := by
  classical
  calc
    (∑ i : Fin S.card, w (enumerate S i)) = ∑ a : S, w a :=
      Equiv.sum_comp (Finset.equivFin S).symm (fun a : S => w a)
    _ = ∑ a ∈ S, w a := Finset.sum_attach _ _

lemma enumerate_fiber_card {α β : Type*} [DecidableEq α] (S : Finset α)
    (p : α → β) (b : β) :
    Set.ncard {i : Fin S.card | p (enumerate S i) = b} =
      (S.filter fun a => p a = b).card := by
  classical
  have he : enumerate S '' {i : Fin S.card | p (enumerate S i) = b} =
      (S.filter (fun a => p a = b) : Set α) := by
    ext a
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_filter.mpr ⟨enumerate_mem S i, hi⟩
    · intro ha
      obtain ⟨haS, hap⟩ := Finset.mem_filter.mp ha
      obtain ⟨i, rfl⟩ := exists_enumerate S haS
      exact ⟨i, hap, rfl⟩
  rw [← Set.ncard_image_of_injective _ (enumerate_injective S), he, Set.ncard_coe_finset]

/-- Enumerate exactly the occupied cover vertices; balance transfers to their assigned fibers. -/
theorem reindex_balanced {α β : Type*} [DecidableEq α]
    (S : Finset α) (p : α → β) (R : ℝ) (hbal : Balanced S p R) :
    ∃ (N : ℕ) (e : Fin N → β) (f : Fin S.card → Fin N),
      Function.Injective e ∧ (∀ i, e (f i) = p (enumerate S i)) ∧
      ∀ k k', (Set.ncard {i | f i = k} : ℝ) ≤ R * Set.ncard {i | f i = k'} := by
  classical
  let C := S.image p
  let e := enumerate C
  let f : Fin S.card → Fin C.card := fun i => Finset.equivFin C
    ⟨p (enumerate S i), Finset.mem_image.mpr ⟨enumerate S i, enumerate_mem S i, rfl⟩⟩
  have hef (i) : e (f i) = p (enumerate S i) := by simp [e, f, enumerate]
  refine ⟨C.card, e, f, enumerate_injective C, hef, ?_⟩
  have hcard (k : Fin C.card) : Set.ncard {i | f i = k} =
      (S.filter fun a => p a = e k).card := by
    have heq : {i | f i = k} = {i | p (enumerate S i) = e k} := by
      ext i
      change f i = k ↔ p (enumerate S i) = e k
      rw [← hef i]
      exact (enumerate_injective C).eq_iff.symm
    rw [heq]
    convert enumerate_fiber_card S p (e k) using 1 <;> congr 2
  intro k k'
  obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp (enumerate_mem C k)
  obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp (enumerate_mem C k')
  rw [hcard, hcard]
  change ((S.filter fun i => p i = enumerate C k).card : ℝ) ≤
    R * (S.filter fun i => p i = enumerate C k').card
  rw [← hea, ← heb]
  convert hbal a ha b hb using 1 <;> unfold leafFiber <;> congr 2

end

end WangZahlLot.Obl.wz_tower_balanced_refinement
