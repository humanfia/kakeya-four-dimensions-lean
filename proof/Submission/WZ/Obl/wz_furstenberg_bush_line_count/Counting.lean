-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_bush_line_count.Counting.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Counting lemmas for `Set.ncard`

Unions over a finset, disjoint unions, and fibres of a relation.

Ported from session x0394 (o141, commit d684c60).
-/

namespace WangZahlLot.Obl.wz_furstenberg_bush_line_count

open scoped Classical

lemma ncard_biUnion_finset_le {ι α : Type*} (F : Finset ι) (S : ι → Set α) :
    ((⋃ i ∈ F, S i).ncard : ℝ) ≤ ∑ i ∈ F, ((S i).ncard : ℝ) := by
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F haF ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert haF]
    have h1 : (((S a) ∪ ⋃ i ∈ F, S i).ncard : ℝ) ≤ ((S a).ncard : ℝ) + ((⋃ i ∈ F, S i).ncard : ℝ) := by
      exact_mod_cast Set.ncard_union_le _ _
    linarith

lemma sum_ncard_le_of_pairwiseDisjoint {ι α : Type*} (F : Finset ι) (S : ι → Set α)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (T : Set α) (hT : T.Finite) (hsub : ∀ i ∈ F, S i ⊆ T) :
    ∑ i ∈ F, ((S i).ncard : ℝ) ≤ (T.ncard : ℝ) := by
  have key : ∀ F' : Finset ι, F' ⊆ F →
      ∑ i ∈ F', ((S i).ncard : ℝ) = ((⋃ i ∈ F', S i).ncard : ℝ) := by
    intro F'
    induction F' using Finset.induction_on with
    | empty => simp
    | insert a F' haF ih =>
      intro hsubF
      rw [Finset.sum_insert haF, Finset.set_biUnion_insert]
      have haF' : a ∈ F := hsubF (Finset.mem_insert_self _ _)
      have hF'F : F' ⊆ F := (Finset.subset_insert _ _).trans hsubF
      rw [ih hF'F]
      have hdis : Disjoint (S a) (⋃ i ∈ F', S i) := by
        rw [Set.disjoint_iUnion_right]; intro i
        rw [Set.disjoint_iUnion_right]; intro hi
        exact hdisj a haF' i (hF'F hi) (fun h => haF (h ▸ hi))
      have hfa : (S a).Finite := hT.subset (hsub a haF')
      have hfU : (⋃ i ∈ F', S i).Finite :=
        hT.subset (Set.iUnion₂_subset (fun i hi => hsub i (hF'F hi)))
      rw [Set.ncard_union_eq hdis hfa hfU]
      push_cast; ring
  rw [key F le_rfl]
  exact_mod_cast Set.ncard_le_ncard (Set.iUnion₂_subset hsub) hT

/-- Fibres: the size of a relation is the sum of the sizes of its rows. -/
lemma ncard_eq_sum_fibers {α β : Type*} {G : Set α} (hG : G.Finite)
    {H : Set (α × β)} (hHfin : H.Finite) (hH : ∀ p ∈ H, p.1 ∈ G) :
    (H.ncard : ℝ) = ∑ b ∈ hG.toFinset, ({b' | (b, b') ∈ H}.ncard : ℝ) := by
  have h1 : H.ncard = hHfin.toFinset.card := Set.ncard_eq_toFinset_card H hHfin
  have h2 := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := hHfin.toFinset)
    (t := hG.toFinset) (fun p hp => by
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hp ⊢; exact hH p hp)
  rw [h1, h2]
  push_cast
  apply Finset.sum_congr rfl
  intro b _
  have : ({b' | (b, b') ∈ H} : Set β).ncard = (hHfin.toFinset.filter (fun p => p.1 = b)).card := by
    rw [← Set.ncard_coe_finset]
    have himg : ((hHfin.toFinset.filter (fun p => p.1 = b) : Finset (α × β)) : Set (α × β)) =
        (fun b' => (b, b')) '' {b' | (b, b') ∈ H} := by
      ext ⟨x, y⟩
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨hp, rfl⟩; exact ⟨y, hp, rfl, rfl⟩
      · rintro ⟨z, hz, rfl, rfl⟩; exact ⟨hz, rfl⟩
    rw [himg, Set.ncard_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)]
  exact_mod_cast this.symm

end WangZahlLot.Obl.wz_furstenberg_bush_line_count
