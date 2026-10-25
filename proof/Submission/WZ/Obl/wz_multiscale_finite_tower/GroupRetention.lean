-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GroupRetention.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GroupBalance

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)
open WangZahlLot.Obl.wz_nsp_full_counted_hierarchy (branchFiber)

lemma GroupedSelection.parent_group_retention {J k : ℕ} {T : TubeHierarchy J}
    {H B R A lam : ℝ} (G : GroupedSelection (T.parent k) H B) (hk : k < J)
    (hB : 0 < B) (hR : 0 ≤ R) (hA : 0 ≤ A) (hlam : 0 ≤ lam)
    (hbal : ∀ j, j ≤ J → Balanced Finset.univ (T.ancestor j) R)
    (S : Finset (Fin (T.layer J).card))
    (hSU : ∀ i ∈ S, T.ancestor (k + 1) i ∈ G.selected)
    (hSbal : Balanced S (T.ancestor k) A)
    (hcard : lam * (T.layer J).card ≤ S.card)
    {i : Fin (T.layer J).card} (hi : i ∈ S) :
    lam * ((Finset.univ.filter fun a => T.ancestor (k + 1) a ∈ G.selected ∧
      T.ancestor k a = T.ancestor k i).image (G.group ∘ T.ancestor (k + 1))).card ≤
      (R * A * (B * R)) * ((leafFiber S (T.ancestor k) i).image
        (G.group ∘ T.ancestor (k + 1))).card := by
  classical
  let U := Finset.univ.filter fun a => T.ancestor (k + 1) a ∈ G.selected ∧ T.ancestor k a = T.ancestor k i
  let V := leafFiber S (T.ancestor k) i
  have hVU : V ⊆ U := by
    intro a ha
    have ha' : a ∈ S ∧ T.ancestor k a = T.ancestor k i := by simpa [V, leafFiber] using ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSU a ha'.1, ha'.2⟩
  have hiV : i ∈ V := by simp only [V, leafFiber, Finset.mem_filter, hi, and_true]
  have hUle : U.card ≤ (leafFiber Finset.univ (T.ancestor k) i).card := by
    apply Finset.card_le_card
    intro a ha
    simpa only [leafFiber, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.mem_filter.mp ha).2.2
  have hret := balanced_leaf_retention Finset.univ S (T.ancestor k) (Finset.subset_univ _)
    hR hA hlam (hbal k hk.le) hSbal
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hcard) hi
  have hret' : lam * U.card ≤ (R * A) * V.card :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hUle) hlam).trans hret
  have hh := branch_retention_of_leaf_retention U V (fun _ => ())
    (G.group ∘ T.ancestor (k + 1)) hVU (fun _ _ _ => rfl)
    (mul_nonneg hB.le hR) (mul_nonneg hR hA) hlam
    (G.group_leaf_balance hk hB hR (hbal (k + 1) (by omega)) (T.ancestor k i)) hiV
    (by simpa only [leafFiber, Finset.filter_true] using hret')
  simpa [branchFiber, leafFiber, U, V] using hh

lemma GroupedSelection.parent_group_image {J k : ℕ} {T : TubeHierarchy J}
    {H B : ℝ} (G : GroupedSelection (T.parent k) H B) (hk : k < J)
    (t : Fin (T.layer k).card) :
    (((Finset.univ.filter fun a => T.ancestor (k + 1) a ∈ G.selected ∧
      T.ancestor k a = t).image (G.group ∘ T.ancestor (k + 1))) : Set _) =
      {j | j ∈ G.selected ∧ G.group j = j ∧ T.parent k j = t} := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨_, has, hat⟩ := Finset.mem_filter.mp ha
    exact ⟨G.group_mem _ has, G.group_idem _ has,
      (G.parent_group _).trans ((T.coherent k hk a).trans hat)⟩
  · rintro ⟨hj, hgj, hpj⟩
    obtain ⟨a, ha⟩ := T.active (k + 1) (by omega) j
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simpa only [ha] using hj,
      by rw [← T.coherent k hk, ha, hpj]⟩, by simpa only [Function.comp_apply, ha] using hgj⟩

lemma RestrictedGrouping.coarse_image {J k : ℕ} {T : TubeHierarchy J} {H B r : ℝ}
    {G : GroupedSelection (T.parent k) H B} {S : Finset (Fin (T.layer J).card)}
    {R : HierarchyRestriction T S} (I : RestrictedGrouping T G R r) (hk : k < J)
    (t : Fin (R.tree.layer k).card) :
    I.map '' {j | I.upper j = t} =
      ((S.filter fun a => T.ancestor k a = R.map k t).image
        (G.group ∘ T.ancestor (k + 1)) : Set _) := by
  classical
  ext j
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb⟩ := I.lower_surjective a
    obtain ⟨c, hc⟩ := R.tree.active (k + 1) (by omega) b
    have hlabel : G.group (T.ancestor (k + 1) (R.map J c)) = I.map a := by
      rw [← R.ancestor, hc, ← I.lower_map, hb]
    refine Finset.mem_image.mpr ⟨R.map J c, Finset.mem_filter.mpr ⟨R.bottom_mem c, ?_⟩, hlabel⟩
    rw [← T.coherent k hk, ← G.parent_group, hlabel, ← I.upper_map, ha]
  · intro hj
    obtain ⟨a, ha, hlabel⟩ := Finset.mem_image.mp hj
    obtain ⟨haS, hat⟩ := Finset.mem_filter.mp ha
    have har : a ∈ Set.range (R.map J) := by rw [R.bottom_image]; exact haS
    obtain ⟨c, rfl⟩ := har
    refine ⟨I.lower (R.tree.ancestor (k + 1) c), ?_, ?_⟩
    · apply R.injective k
      rw [I.upper_map, I.lower_map, R.ancestor, G.parent_group, T.coherent k hk, hat]
    · simpa only [Function.comp_apply, I.lower_map, R.ancestor] using hlabel

lemma RestrictedGrouping.coarse_retention {J k : ℕ} {T : TubeHierarchy J}
    {H B r A C lam : ℝ} {G : GroupedSelection (T.parent k) H B}
    {S : Finset (Fin (T.layer J).card)} {R : HierarchyRestriction T S}
    (I : RestrictedGrouping T G R r) (hk : k < J)
    (hB : 0 < B) (hA : 0 ≤ A) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hbal : ∀ j, j ≤ J → Balanced Finset.univ (T.ancestor j) A)
    (hSU : ∀ i ∈ S, T.ancestor (k + 1) i ∈ G.selected)
    (hSbal : Balanced S (T.ancestor k) C)
    (hcard : lam * (T.layer J).card ≤ S.card) (t : Fin (R.tree.layer k).card) :
    lam * {j | j ∈ G.selected ∧ G.group j = j ∧ T.parent k j = R.map k t}.ncard ≤
      (A * C * (B * A)) * {j | I.upper j = t}.ncard := by
  classical
  obtain ⟨a, ha⟩ := R.tree.active k hk.le t
  have hat : T.ancestor k (R.map J a) = R.map k t := by rw [← R.ancestor, ha]
  have hh := G.parent_group_retention hk hB hA hC hlam hbal S hSU hSbal hcard (R.bottom_mem a)
  rw [← Set.ncard_coe_finset, G.parent_group_image hk, hat] at hh
  have hf : leafFiber S (T.ancestor k) (R.map J a) = S.filter (fun a => T.ancestor k a = R.map k t) := by
    ext b
    simp only [leafFiber, Finset.mem_filter, hat]
  rw [hf, ← Set.ncard_coe_finset, ← I.coarse_image hk t,
    Set.ncard_image_of_injective _ I.injective] at hh
  exact hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
