-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GroupedInsertion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GroupedRegularization
import Submission.WZ.Obl.wz_multiscale_finite_tower.InsertCertificate

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement
  (enumerate enumerate_mem enumerate_injective exists_enumerate Balanced leafFiber)

/-- The occupied groups inserted between two restricted levels. -/
structure RestrictedGrouping {J k : ℕ} (T : TubeHierarchy J)
    {H B : ℝ} (G : GroupedSelection (T.parent k) H B)
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S) (r : ℝ) where
  middle : Layer
  radius : middle.radius = r
  map : Fin middle.card → Fin (T.layer (k + 1)).card
  injective : Function.Injective map
  position : ∀ i, middle.position i = (T.layer (k + 1)).position (map i)
  direction : ∀ i, middle.direction i = (T.layer (k + 1)).direction (map i)
  lower : Fin (R.tree.layer (k + 1)).card → Fin middle.card
  lower_surjective : Function.Surjective lower
  lower_map : ∀ i, map (lower i) = G.group (R.map (k + 1) i)
  upper : Fin middle.card → Fin (R.tree.layer k).card
  upper_map : ∀ i, R.map k (upper i) = T.parent k (map i)
  commute : ∀ i, upper (lower i) = R.tree.parent k i
  selected : ∀ i, map i ∈ G.selected
  fixed : ∀ i, G.group (map i) = map i
  fine_image : ∀ i, R.map (k + 1) '' {j | lower j = i} =
    {j | j ∈ G.selected ∧ G.group j = map i}

theorem exists_restricted_grouping {J k : ℕ} {T : TubeHierarchy J} {H B : ℝ}
    (G : GroupedSelection (T.parent k) H B) (hk : k < J)
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S)
    (hSU : ∀ i ∈ S, T.ancestor (k + 1) i ∈ G.selected)
    (hclosed : ∀ i, T.ancestor (k + 1) i ∈ G.selected → ∀ i', T.ancestor (k + 1) i' ∈ G.selected →
      G.group (T.ancestor (k + 1) i) = G.group (T.ancestor (k + 1) i') → (i ∈ S ↔ i' ∈ S))
    (r : ℝ) : Nonempty (RestrictedGrouping T G R r) := by
  classical
  have hS : S.Nonempty := ⟨R.map J ⟨0, (R.tree.layer J).card_pos⟩, R.bottom_mem _⟩
  let V := (S.image (T.ancestor (k + 1))).image G.group
  have hV : V.Nonempty := (hS.image _).image _
  let M : Layer := ⟨r, V.card, Finset.card_pos.mpr hV,
    (T.layer (k + 1)).position ∘ enumerate V,
    (T.layer (k + 1)).direction ∘ enumerate V,
    fun i => (T.layer (k + 1)).unit (enumerate V i)⟩
  have hchild (i : Fin (R.tree.layer (k + 1)).card) :
      R.map (k + 1) i ∈ S.image (T.ancestor (k + 1)) := by
    change R.map (k + 1) i ∈ (S.image (T.ancestor (k + 1)) : Set _)
    rw [← R.image]
    exact ⟨i, rfl⟩
  have hchildsel (i : Fin (R.tree.layer (k + 1)).card) : R.map (k + 1) i ∈ G.selected := by
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (hchild i)
    exact he ▸ hSU a ha
  have hlower (i : Fin (R.tree.layer (k + 1)).card) :
      ∃ a : Fin M.card, enumerate V a = G.group (R.map (k + 1) i) :=
    exists_enumerate V (Finset.mem_image.mpr ⟨_, hchild i, rfl⟩)
  choose a ha using hlower
  have hasurj : Function.Surjective a := by
    intro b
    obtain ⟨j, hj, hgj⟩ := Finset.mem_image.mp (enumerate_mem V b)
    have hj' : j ∈ Set.range (R.map (k + 1)) := by rw [R.image]; exact hj
    obtain ⟨i, rfl⟩ := hj'
    exact ⟨i, enumerate_injective V ((ha i).trans hgj)⟩
  have hmparent (i : Fin M.card) : T.parent k (enumerate V i) ∈ Set.range (R.map k) := by
    obtain ⟨j, rfl⟩ := hasurj i
    rw [ha, G.parent_group, ← R.parent k hk]
    exact ⟨R.tree.parent k j, rfl⟩
  choose b hb using hmparent
  have hcomm (i) : b (a i) = R.tree.parent k i := by
    apply R.injective k
    rw [hb, ha, G.parent_group, R.parent k hk]
  have hselected (i : Fin M.card) : enumerate V i ∈ G.selected := by
    obtain ⟨j, rfl⟩ := hasurj i
    rw [ha]
    exact G.group_mem _ (hchildsel j)
  have hfixed (i : Fin M.card) : G.group (enumerate V i) = enumerate V i := by
    obtain ⟨j, rfl⟩ := hasurj i
    rw [ha]
    exact G.group_idem _ (hchildsel j)
  refine ⟨⟨M, rfl, enumerate V, enumerate_injective V, (fun _ => rfl), (fun _ => rfl),
    a, hasurj, ha, b, hb, hcomm, hselected, hfixed, ?_⟩⟩
  intro i
  ext j
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨hchildsel t, (ha t).symm.trans (congrArg (enumerate V) ht)⟩
  · rintro ⟨hj, hgj⟩
    obtain ⟨t, ht⟩ := hasurj i
    obtain ⟨z, hz, hzchild⟩ := Finset.mem_image.mp (hchild t)
    obtain ⟨z', hz'⟩ := T.active (k + 1) (by omega) j
    have hz'sel : T.ancestor (k + 1) z' ∈ G.selected := hz' ▸ hj
    have hgzz' : G.group (T.ancestor (k + 1) z) = G.group (T.ancestor (k + 1) z') := by
      rw [hzchild, hz', hgj, ← ha, ht]
    have hz'S : z' ∈ S := (hclosed z (hSU z hz) z' hz'sel hgzz').mp hz
    have hjrange : j ∈ Set.range (R.map (k + 1)) := by
      rw [R.image]
      exact Finset.mem_image.mpr ⟨z', hz'S, hz'⟩
    obtain ⟨j', rfl⟩ := hjrange
    exact ⟨j', enumerate_injective V ((ha j').trans hgj), rfl⟩

lemma RestrictedGrouping.fine_card {J k : ℕ} {T : TubeHierarchy J} {H B r : ℝ}
    {G : GroupedSelection (T.parent k) H B} {S : Finset (Fin (T.layer J).card)}
    {R : HierarchyRestriction T S} (I : RestrictedGrouping T G R r) (i : Fin I.middle.card) :
    {j | I.lower j = i}.ncard = {j | j ∈ G.selected ∧ G.group j = I.map i}.ncard := by
  rw [← I.fine_image i, Set.ncard_image_of_injective _ (R.injective (k + 1))]

end WangZahlLot.Obl.wz_multiscale_finite_tower
