-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.CoverGrouping.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GroupedGeometry
import Submission.WZ.Obl.wz_multiscale_finite_tower.BalancedRepresentativeCovers
import Submission.WZ.Obl.wz_multiscale_finite_tower.FibreEnumeration

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya

structure IndexedCovers {J : ℕ} (T : TubeHierarchy J) (k : ℕ)
    (d θ ζ C ω H B : ℝ) (Y : Fin (T.layer (k + 1)).card → Set Space) where
  card : Fin (T.layer k).card → ℕ
  index : ∀ t, Fin (card t) → Fin (T.layer (k + 1)).card
  injective : ∀ t, Function.Injective (index t)
  image : ∀ t, Set.range (index t) = {i | T.parent k i = t}
  frame : ∀ t, PhysicalFrame d (T.layer k).radius (T.layer (k + 1)).radius θ
    ((T.layer k).position t) ((T.layer k).direction t) (card t)
    ((T.layer (k + 1)).position ∘ index t) ((T.layer (k + 1)).direction ∘ index t) (Y ∘ index t)
  cover : ∀ t, BalancedPhysicalCover d (T.layer k).radius (T.layer (k + 1)).radius ζ C ω H B
    (card t) ((T.layer (k + 1)).position ∘ index t) ((T.layer (k + 1)).direction ∘ index t)

lemma IndexedCovers.parent {J k : ℕ} {T : TubeHierarchy J} {d θ ζ C ω H B : ℝ}
    {Y : Fin (T.layer (k + 1)).card → Set Space} (D : IndexedCovers T k d θ ζ C ω H B Y)
    (t) (i : Fin (D.card t)) : T.parent k (D.index t i) = t := by
  have hi : D.index t i ∈ Set.range (D.index t) := ⟨i, rfl⟩
  simpa only [D.image, Set.mem_setOf_eq] using hi

lemma IndexedCovers.card_eq {J k : ℕ} {T : TubeHierarchy J} {d θ ζ C ω H B : ℝ}
    {Y : Fin (T.layer (k + 1)).card → Set Space} (D : IndexedCovers T k d θ ζ C ω H B Y)
    (t) : D.card t = {i | T.parent k i = t}.ncard := by
  rw [← D.image, Set.ncard_range_of_injective (D.injective t), Nat.card_fin]

/-- The local disjoint covers give one global grouping of the child indices. -/
theorem IndexedCovers.grouping {J k : ℕ} {T : TubeHierarchy J} {d θ ζ C ω H B : ℝ}
    {Y : Fin (T.layer (k + 1)).card → Set Space} (D : IndexedCovers T k d θ ζ C ω H B Y)
    (P : Finset (Fin (T.layer k).card)) :
    ∃ G : GroupedSelection (T.parent k) H B, G.parents = P ∧
      (∀ t i, D.index t i ∈ G.selected ↔ t ∈ P ∧ i ∈ (D.cover t).selected) ∧
      (∀ t i, G.group (D.index t i) = D.index t ((D.cover t).representative ((D.cover t).assign i))) := by
  classical
  let E := fibreEquiv (T.parent k) D.card D.index D.injective D.image
  have hE (t) (i : Fin (D.card t)) : E ⟨t, i⟩ = D.index t i := rfl
  let g : Fin (T.layer (k + 1)).card → Fin (T.layer (k + 1)).card := fun i =>
    let a := E.symm i
    D.index a.1 ((D.cover a.1).representative ((D.cover a.1).assign a.2))
  let S := Finset.univ.filter fun i =>
    let a := E.symm i
    a.1 ∈ P ∧ a.2 ∈ (D.cover a.1).selected
  have hg (t) (i : Fin (D.card t)) : g (D.index t i) =
      D.index t ((D.cover t).representative ((D.cover t).assign i)) := by
    change (fun a : Σ t, Fin (D.card t) => D.index a.1
      ((D.cover a.1).representative ((D.cover a.1).assign a.2))) (E.symm (E ⟨t, i⟩)) = _
    rw [E.symm_apply_apply]
  have hS (t) (i : Fin (D.card t)) : D.index t i ∈ S ↔ t ∈ P ∧ i ∈ (D.cover t).selected := by
    change (E ⟨t, i⟩ ∈ S) ↔ _
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    change (fun a : Σ t, Fin (D.card t) => a.1 ∈ P ∧ a.2 ∈ (D.cover a.1).selected)
      (E.symm (E ⟨t, i⟩)) ↔ _
    rw [E.symm_apply_apply]
  have hgpar (i) : T.parent k (g i) = T.parent k i := by
    obtain ⟨⟨t, a⟩, rfl⟩ := E.surjective i
    rw [hE, hg, D.parent, D.parent]
  have hsim (t) (ht : t ∈ P) :
      D.index t '' ((D.cover t).selected : Set _) = {i | i ∈ S ∧ T.parent k i = t} := by
    ext i
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(hS t a).mpr ⟨ht, ha⟩, D.parent t a⟩
    · rintro ⟨hi, hpi⟩
      have hir : i ∈ Set.range (D.index t) := by rw [D.image]; exact hpi
      obtain ⟨a, rfl⟩ := hir
      exact ⟨a, ((hS t a).mp hi).2, rfl⟩
  have hfine (t) (ht : t ∈ P) (a : Fin (D.cover t).card) :
      D.index t '' {i | i ∈ (D.cover t).selected ∧ (D.cover t).assign i = a} =
        {i | i ∈ S ∧ g i = D.index t ((D.cover t).representative a)} := by
    ext i
    constructor
    · rintro ⟨b, ⟨hb, hba⟩, rfl⟩
      exact ⟨(hS t b).mpr ⟨ht, hb⟩, by rw [hg, hba]⟩
    · rintro ⟨hi, hgi⟩
      have hpi : T.parent k i = t := by
        rw [← hgpar, hgi, D.parent]
      have hir : i ∈ Set.range (D.index t) := by rw [D.image]; exact hpi
      obtain ⟨b, rfl⟩ := hir
      have he : (D.cover t).assign b = a := by
        rw [hg] at hgi
        have hh := congrArg (D.cover t).assign (D.injective t hgi)
        simpa only [(D.cover t).representative_assign] using hh
      exact ⟨b, ⟨((hS t b).mp hi).2, he⟩, rfl⟩
  have hfilter (t) (ht : t ∈ P) (a : Fin (D.cover t).card) :
      (S.filter fun i => g i = D.index t ((D.cover t).representative a)).card =
        ((D.cover t).selected.filter fun i => (D.cover t).assign i = a).card := by
    have he :
        ((S.filter fun i => g i = D.index t ((D.cover t).representative a)) : Set _) =
          {i | i ∈ S ∧ g i = D.index t ((D.cover t).representative a)} := by ext i; simp
    have he' : (((D.cover t).selected.filter fun i => (D.cover t).assign i = a) : Set _) =
        {i | i ∈ (D.cover t).selected ∧ (D.cover t).assign i = a} := by ext i; simp
    rw [← Set.ncard_coe_finset, he, ← hfine t ht a,
      Set.ncard_image_of_injective _ (D.injective t), ← he', Set.ncard_coe_finset]
  refine ⟨{
    parents := P
    selected := S
    group := g
    parent_group := hgpar
    selected_parent := ?_
    group_mem := ?_
    group_idem := ?_
    retained := ?_
    balanced := ?_ }, rfl, hS, hg⟩
  · intro i hi
    obtain ⟨⟨t, a⟩, rfl⟩ := E.surjective i
    rw [hE, D.parent]
    exact ((hS t a).mp hi).1
  · intro i hi
    obtain ⟨⟨t, a⟩, rfl⟩ := E.surjective i
    rw [hE, hg, hS]
    exact ⟨((hS t a).mp hi).1, (D.cover t).representative_mem _⟩
  · intro i hi
    obtain ⟨⟨t, a⟩, rfl⟩ := E.surjective i
    change g (g (D.index t a)) = g (D.index t a)
    rw [hg t a, hg t ((D.cover t).representative ((D.cover t).assign a)), (D.cover t).representative_assign]
  · intro t ht
    have he : (S.filter (fun i => T.parent k i = t) : Set _) =
        {i | i ∈ S ∧ T.parent k i = t} := by ext i; simp
    have hf : (Finset.univ.filter (fun i => T.parent k i = t) : Set _) =
        {i | T.parent k i = t} := by ext i; simp
    have hcs : (S.filter (fun i => T.parent k i = t)).card = (D.cover t).selected.card := by
      rw [← Set.ncard_coe_finset, he, ← hsim t ht,
        Set.ncard_image_of_injective _ (D.injective t), Set.ncard_coe_finset]
    have hcf : (Finset.univ.filter (fun i => T.parent k i = t)).card = D.card t := by
      rw [← Set.ncard_coe_finset, hf, ← D.card_eq t]
    rw [hcs, hcf]
    exact (D.cover t).retained
  · intro i hi j hj hp
    obtain ⟨⟨t, a⟩, rfl⟩ := E.surjective i
    obtain ⟨⟨t', b⟩, rfl⟩ := E.surjective j
    have htt : t = t' := by simpa only [hE, D.parent] using hp
    subst t'
    have ha := (hS t a).mp hi
    have hb := (hS t b).mp hj
    rw [hE, hE, hg, hg, hfilter t ha.1, hfilter t ha.1]
    exact (D.cover t).balanced _ _

end WangZahlLot.Obl.wz_multiscale_finite_tower
