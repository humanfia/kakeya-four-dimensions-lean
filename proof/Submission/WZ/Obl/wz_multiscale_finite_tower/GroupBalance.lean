-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GroupBalance.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GroupedInsertion

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)

lemma leafFiber_card_reindex {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : Finset β) (e : α → β)
    (he : Function.Injective e) (hrange : Set.range e = (S : Set β))
    (p : β → γ) (i : α) :
    (leafFiber Finset.univ (p ∘ e) i).card = (leafFiber S p (e i)).card := by
  classical
  have himage : e '' (leafFiber Finset.univ (p ∘ e) i : Set α) =
      (leafFiber S p (e i) : Set β) := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ham : e a ∈ S := by
        change e a ∈ (S : Set β)
        rw [← hrange]
        exact ⟨a, rfl⟩
      simpa only [leafFiber, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.comp_apply] using And.intro ham ha
    · intro hb
      have hb' : b ∈ S ∧ p b = p (e i) := by simpa only [leafFiber, Finset.mem_coe, Finset.mem_filter] using hb
      have hbr : b ∈ Set.range e := by rw [hrange]; exact hb'.1
      obtain ⟨a, rfl⟩ := hbr
      exact ⟨a, by simpa only [leafFiber, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.comp_apply] using hb'.2, rfl⟩
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ he, himage, Set.ncard_coe_finset]

lemma balanced_reindex_range {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : Finset β) (e : α → β)
    (he : Function.Injective e) (hrange : Set.range e = (S : Set β))
    (p : β → γ) {R : ℝ} (h : Balanced S p R) : Balanced Finset.univ (p ∘ e) R := by
  have hmem (i) : e i ∈ S := by
    change e i ∈ (S : Set β)
    rw [← hrange]
    exact ⟨i, rfl⟩
  intro i hi j hj
  rw [leafFiber_card_reindex S e he hrange p i, leafFiber_card_reindex S e he hrange p j]
  exact h (e i) (hmem i) (e j) (hmem j)

lemma RestrictedGrouping.balanced {J k : ℕ} {T : TubeHierarchy J} {H B r A : ℝ}
    {G : GroupedSelection (T.parent k) H B} {S : Finset (Fin (T.layer J).card)}
    {R : HierarchyRestriction T S} (I : RestrictedGrouping T G R r)
    (h : Balanced S (G.group ∘ T.ancestor (k + 1)) A) :
    Balanced Finset.univ (I.lower ∘ R.tree.ancestor (k + 1)) A := by
  apply (balanced_postcomp_iff Finset.univ _ I.map I.injective A).mp
  have he : I.map ∘ (I.lower ∘ R.tree.ancestor (k + 1)) =
      (G.group ∘ T.ancestor (k + 1)) ∘ R.map J := by
    funext i
    simp only [Function.comp_apply, I.lower_map, R.ancestor]
  rw [he]
  exact balanced_reindex_range S (R.map J) (R.injective J) R.bottom_image _ h

lemma GroupedSelection.group_leaf_balance {J k : ℕ} {T : TubeHierarchy J} {H B R : ℝ}
    (G : GroupedSelection (T.parent k) H B) (hk : k < J) (hB : 0 < B) (hR : 0 ≤ R)
    (hbal : Balanced Finset.univ (T.ancestor (k + 1)) R)
    (t : Fin (T.layer k).card) :
    Balanced (Finset.univ.filter fun i => T.ancestor (k + 1) i ∈ G.selected ∧ T.ancestor k i = t)
      (G.group ∘ T.ancestor (k + 1)) (B * R) := by
  classical
  let p := T.ancestor (k + 1)
  let U := Finset.univ.filter fun i => p i ∈ G.selected ∧ T.ancestor k i = t
  let A (i : Fin (T.layer J).card) := G.selected.filter (fun a => G.group a = G.group (p i))
  let w : Fin (T.layer (k + 1)).card → ℝ := fun a => (Finset.univ.filter fun i => p i = a).card
  have hf (i : Fin (T.layer J).card) :
      (Finset.univ.filter fun a => p a = p i) = leafFiber Finset.univ p i := by
    ext a
    simp [leafFiber]
  have hcomp (a b) : w a ≤ R * w b := by
    obtain ⟨i, rfl⟩ := T.active (k + 1) (by omega) a
    obtain ⟨j, rfl⟩ := T.active (k + 1) (by omega) b
    change ((Finset.univ.filter fun a => p a = p i).card : ℝ) ≤
      R * (Finset.univ.filter fun a => p a = p j).card
    rw [hf i, hf j]
    exact hbal i (Finset.mem_univ _) j (Finset.mem_univ _)
  have he (i) (hi : i ∈ U) :
      leafFiber U (G.group ∘ p) i = Finset.univ.filter (fun a => p a ∈ A i) := by
    have hit : T.ancestor k i = t := (Finset.mem_filter.mp hi).2.2
    ext a
    simp only [leafFiber, U, A, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨ha, hg⟩
      refine ⟨⟨ha, ?_⟩, hg⟩
      have hh := congrArg (T.parent k) hg
      simpa only [G.parent_group, p, T.coherent k hk, hit] using hh
  intro i hi j hj
  change ((leafFiber U (G.group ∘ p) i).card : ℝ) ≤ B * R * (leafFiber U (G.group ∘ p) j).card
  rw [he i hi, he j hj, card_preimage_eq_sum, card_preimage_eq_sum]
  apply weighted_card_comparison (A i) (A j) w hR hB
  · exact ⟨p j, by simp only [A, Finset.mem_filter, and_true]; exact (Finset.mem_filter.mp hj).2.1⟩
  · intro a ha
    exact Nat.cast_nonneg _
  · intro a ha b hb
    exact hcomp a b
  · apply G.balanced (p i) (Finset.mem_filter.mp hi).2.1 (p j) (Finset.mem_filter.mp hj).2.1
    change T.parent k (T.ancestor (k + 1) i) = T.parent k (T.ancestor (k + 1) j)
    rw [T.coherent k hk, T.coherent k hk]
    exact (Finset.mem_filter.mp hi).2.2.trans (Finset.mem_filter.mp hj).2.2.symm

end WangZahlLot.Obl.wz_multiscale_finite_tower
