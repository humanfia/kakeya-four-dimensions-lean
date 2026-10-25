-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/GridPacketRestriction.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.UniformGridRefinement

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.GridPacketRestriction

open UniformGridRefinement Submission.Obl.k4_finite_forest_width_selection

/-- Keep precisely the packets at the old grid nodes, recording their old level. -/
abbrev Packets {C : ℕ} (lev : Fin C → ℕ) (m k : ℕ) :=
  (i : Fin m) × {b : Fin C // lev b = coarseIndex k i.val}

def old {C m k : ℕ} {lev : Fin C → ℕ} (a : Packets lev m k) : Fin C := a.2.val

theorem old_level {C m k : ℕ} {lev : Fin C → ℕ} (a : Packets lev m k) :
    lev (old a) = coarseIndex k a.1.val := a.2.property

theorem old_injective {C m k : ℕ} {lev : Fin C → ℕ} (hk : 0 < k) :
    Function.Injective (old (lev := lev) (m := m) (k := k)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hab
  change a.val = b.val at hab
  have hij : i = j := Fin.ext (coarseIndex_injective k hk
    (a.property.symm.trans ((congrArg lev hab).trans b.property)))
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext hab)

theorem card_packets_le {C m k : ℕ} {lev : Fin C → ℕ} (hk : 0 < k) :
    Fintype.card (Packets lev m k) ≤ C := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective (old (lev := lev) (m := m) (k := k)) (old_injective hk)

/-- The new parent follows the actual original ancestor chain to the preceding
retained grid node. The first retained layer needs no parent condition. -/
noncomputable def parent {C m k : ℕ} {lev : Fin C → ℕ} (par : Fin C → Fin C)
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (a : Packets lev m k) : Packets lev m k :=
  if hi : 0 < a.1.val then
    let ip : Fin m := ⟨a.1.val - 1, (Nat.sub_le _ _).trans_lt a.1.isLt⟩
    have htarget : coarseIndex k ip.val ≤ lev (old a) := by
      rw [old_level a]
      exact coarseIndex_monotone k (Nat.sub_le _ _)
    ⟨ip, ⟨forestAncestor lev par (old a) (coarseIndex k ip.val),
      forestAncestor_level hpar _ _ htarget⟩⟩
  else a

theorem parent_level {C m k : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (a : Packets lev m k) (hi : 0 < a.1.val) :
    (parent par hpar a).1.val + 1 = a.1.val := by
  simp only [parent, hi, dite_true]
  omega

theorem parent_old_eq {C m k : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (a : Packets lev m k) (hi : 0 < a.1.val) :
    old (parent par hpar a) =
      forestAncestor lev par (old a) (coarseIndex k (a.1.val - 1)) := by
  simp only [parent, hi, dite_true]
  rfl

/-- Every original transitive parent property survives restriction to the grid. -/
theorem parent_relation {C m k : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (R : Fin C → Fin C → Prop) (hrefl : ∀ b, R b b)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ b, 0 < lev b → R b (par b))
    (a : Packets lev m k) (hi : 0 < a.1.val) :
    R (old a) (old (parent par hpar a)) := by
  rw [parent_old_eq hpar a hi]
  exact forest_ancestor_relation hpar R hrefl htrans hstep _ _

/-- Restricting to the retained nodes preserves every original level sum
exactly. In particular, no mass or prior is renormalized. -/
theorem sum_level {C m k : ℕ} {lev : Fin C → ℕ} (hk : 0 < k)
    {M : Type*} [AddCommMonoid M] (f : Fin C → M) (i : ℕ) (hi : i < m) :
    (∑ a : Packets lev m k, if a.1.val = i then f (old a) else 0) =
      ∑ b : Fin C, if lev b = coarseIndex k i then f b else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun a _ => old a)
  · intro a ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [old_level a, (Finset.mem_filter.mp ha).2]
  · intro a ha b hb hab
    exact old_injective hk hab
  · intro b hb
    let a : Packets lev m k := ⟨⟨i, hi⟩, ⟨b, (Finset.mem_filter.mp hb).2⟩⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
  · intro a _
    rfl

/-- A list on an original observation pulls back through the packet injection. -/
theorem pulled_list_card {C m k : ℕ} {lev : Fin C → ℕ} (hk : 0 < k)
    (S : Finset (Fin C)) (i : ℕ) :
    (Finset.univ.filter (fun a : Packets lev m k => a.1.val = i ∧ old a ∈ S)).card ≤
      S.card := by
  apply Finset.card_le_card_of_injOn old
  · intro a ha
    exact (Finset.mem_filter.mp ha).2.2
  · intro a ha b hb hab
    exact old_injective hk hab

abbrev count {C : ℕ} (lev : Fin C → ℕ) (m k : ℕ) := Fintype.card (Packets lev m k)

noncomputable def enumeration {C : ℕ} (lev : Fin C → ℕ) (m k : ℕ) :
    Fin (count lev m k) ≃ Packets lev m k := (Fintype.equivFin _).symm

noncomputable def index {C m k : ℕ} {lev : Fin C → ℕ}
    (b : Fin (count lev m k)) : Fin C := old (enumeration lev m k b)

noncomputable def level {C m k : ℕ} {lev : Fin C → ℕ}
    (b : Fin (count lev m k)) : ℕ := (enumeration lev m k b).1.val

noncomputable def predecessor {C m k : ℕ} {lev : Fin C → ℕ} (par : Fin C → Fin C)
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (b : Fin (count lev m k)) : Fin (count lev m k) :=
  (enumeration lev m k).symm (parent par hpar (enumeration lev m k b))

theorem index_level {C m k : ℕ} {lev : Fin C → ℕ} (b : Fin (count lev m k)) :
    lev (index b) = coarseIndex k (level b) := old_level _

theorem index_injective {C m k : ℕ} {lev : Fin C → ℕ} (hk : 0 < k) :
    Function.Injective (index (lev := lev) (m := m) (k := k)) :=
  (old_injective hk).comp (enumeration lev m k).injective

theorem level_lt {C m k : ℕ} {lev : Fin C → ℕ} (b : Fin (count lev m k)) :
    level b < m := (enumeration lev m k b).1.isLt

theorem predecessor_level {C m k : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (b : Fin (count lev m k)) (hb : 0 < level b) :
    level (predecessor par hpar b) + 1 = level b := by
  simpa only [level, predecessor, Equiv.apply_symm_apply] using
    parent_level hpar (enumeration lev m k b) hb

theorem predecessor_relation {C m k : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b)
    (R : Fin C → Fin C → Prop) (hrefl : ∀ b, R b b)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hstep : ∀ b, 0 < lev b → R b (par b))
    (b : Fin (count lev m k)) (hb : 0 < level b) :
    R (index b) (index (predecessor par hpar b)) := by
  simpa only [index, predecessor, Equiv.apply_symm_apply] using
    parent_relation hpar R hrefl htrans hstep (enumeration lev m k b) hb

theorem index_surjective_at_level {C m k : ℕ} {lev : Fin C → ℕ}
    (i : ℕ) (hi : i < m) (b : Fin C) (hb : lev b = coarseIndex k i) :
    ∃ b' : Fin (count lev m k), index b' = b ∧ level b' = i := by
  let a : Packets lev m k := ⟨⟨i, hi⟩, ⟨b, hb⟩⟩
  refine ⟨(enumeration lev m k).symm a, ?_, ?_⟩
  · simp only [index, Equiv.apply_symm_apply]
    rfl
  · simp only [level, Equiv.apply_symm_apply]
    rfl

theorem sum_level_fin {C m k : ℕ} {lev : Fin C → ℕ} (hk : 0 < k)
    {M : Type*} [AddCommMonoid M] (f : Fin C → M) (i : ℕ) (hi : i < m) :
    (∑ b : Fin (count lev m k), if level b = i then f (index b) else 0) =
      ∑ b : Fin C, if lev b = coarseIndex k i then f b else 0 := by
  calc
    _ = ∑ a : Packets lev m k, if a.1.val = i then f (old a) else 0 :=
      (enumeration lev m k).sum_comp _
    _ = _ := sum_level hk f i hi

noncomputable def pullList {C m k : ℕ} {lev : Fin C → ℕ}
    (S : Finset (Fin C)) (i : ℕ) : Finset (Fin (count lev m k)) :=
  (Finset.univ.filter (fun a : Packets lev m k => a.1.val = i ∧ old a ∈ S)).map
    (enumeration lev m k).symm.toEmbedding

theorem pullList_card {C m k : ℕ} {lev : Fin C → ℕ} (hk : 0 < k)
    (S : Finset (Fin C)) (i : ℕ) :
    (pullList (lev := lev) (m := m) (k := k) S i).card ≤ S.card := by
  simpa only [pullList, Finset.card_map] using pulled_list_card (lev := lev) (m := m) hk S i

theorem mem_pullList {C m k : ℕ} {lev : Fin C → ℕ} {S : Finset (Fin C)}
    {i : ℕ} {b : Fin (count lev m k)} (hi : level b = i) (hb : index b ∈ S) :
    b ∈ pullList S i := by
  apply Finset.mem_map.mpr
  refine ⟨enumeration lev m k b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hb⟩, ?_⟩
  exact (enumeration lev m k).symm_apply_apply b

end Submission.Obl.k4_isotropic_path_improvement.Repair.GridPacketRestriction
