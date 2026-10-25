-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyRestriction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.IndexTransport
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.RestrictedTree

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)
open WangZahlLot.Obl.wz_nsp_full_counted_hierarchy (branchFiber)
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives (ConvexCount SlabBound)

/-- Restriction to the ancestors of a leaf set keeps all radii and axes. -/
structure HierarchyRestriction {J : ℕ} (T : TubeHierarchy J)
    (S : Finset (Fin (T.layer J).card)) where
  tree : TubeHierarchy J
  map : ∀ j, Fin (tree.layer j).card → Fin (T.layer j).card
  injective : ∀ j, Function.Injective (map j)
  image : ∀ j, Set.range (map j) = (S.image (T.ancestor j) : Set (Fin (T.layer j).card))
  radius : ∀ j, (tree.layer j).radius = (T.layer j).radius
  position : ∀ j i, (tree.layer j).position i = (T.layer j).position (map j i)
  direction : ∀ j i, (tree.layer j).direction i = (T.layer j).direction (map j i)
  parent : ∀ j, j < J → ∀ i, map j (tree.parent j i) = T.parent j (map (j + 1) i)
  ancestor : ∀ j i, map j (tree.ancestor j i) = T.ancestor j (map J i)
  branches : ∀ j, j < J → ∀ k i, i ∈ S → T.ancestor j i = map j k →
    {a | tree.parent j a = k}.ncard = (branchFiber S (T.ancestor j) (T.ancestor (j + 1)) i).card

theorem exists_hierarchy_restriction {J : ℕ} (T : TubeHierarchy J)
    (S : Finset (Fin (T.layer J).card)) (hS : S.Nonempty) :
    Nonempty (HierarchyRestriction T S) := by
  classical
  obtain ⟨k, q, g, hq, hg⟩ :=
    WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.restrict_partition_tower
      (fun j => (T.layer j).card) J T.ancestor T.parent T.coherent S hS
  have hqJ : Set.range (q J) = (S : Set (Fin (T.layer J).card)) := by
    simpa only [T.terminal, Finset.image_id] using (hq J).2.2
  have hex (j : ℕ) (i : Fin (k J)) : ∃ a, q j a = T.ancestor j (q J i) := by
    have hi : q J i ∈ S := by
      change q J i ∈ (S : Set (Fin (T.layer J).card))
      rw [← hqJ]
      exact ⟨i, rfl⟩
    have him : T.ancestor j (q J i) ∈ Set.range (q j) := by
      rw [(hq j).2.2]
      exact Finset.mem_image.mpr ⟨q J i, hi, rfl⟩
    exact him
  choose a ha using hex
  let U : TubeHierarchy J := {
    layer := fun j => ⟨(T.layer j).radius, k j, (hq j).1,
      (T.layer j).position ∘ q j, (T.layer j).direction ∘ q j,
      fun i => (T.layer j).unit (q j i)⟩
    parent := g
    ancestor := a
    terminal := by
      funext i
      apply (hq J).2.1
      simpa only [T.terminal, id_eq] using ha J i
    coherent := by
      intro j hj i
      apply (hq j).2.1
      rw [(hg j hj).1, ha, T.coherent j hj, ha]
    active := by
      intro j hj t
      have ht : q j t ∈ S.image (T.ancestor j) := by
        change q j t ∈ (S.image (T.ancestor j) : Set (Fin (T.layer j).card))
        rw [← (hq j).2.2]
        exact ⟨t, rfl⟩
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp ht
      have hiq : i ∈ Set.range (q J) := by rw [hqJ]; exact hi
      obtain ⟨b, hb⟩ := hiq
      refine ⟨b, (hq j).2.1 ?_⟩
      rw [ha, hb, he] }
  exact ⟨⟨U, q, (fun j => (hq j).2.1), (fun j => (hq j).2.2), (fun _ => rfl),
    (fun _ _ => rfl), (fun _ _ => rfl), (fun j hj => (hg j hj).1), ha,
    (fun j hj => (hg j hj).2)⟩⟩

lemma HierarchyRestriction.bottom_image {J : ℕ} {T : TubeHierarchy J}
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S) :
    Set.range (R.map J) = (S : Set (Fin (T.layer J).card)) := by
  simpa only [T.terminal, Finset.image_id] using R.image J

lemma HierarchyRestriction.bottom_mem {J : ℕ} {T : TubeHierarchy J}
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S)
    (i : Fin (R.tree.layer J).card) : R.map J i ∈ S := by
  change R.map J i ∈ (S : Set (Fin (T.layer J).card))
  rw [← R.bottom_image]
  exact ⟨i, rfl⟩

lemma HierarchyRestriction.bottom_card {J : ℕ} {T : TubeHierarchy J}
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S) :
    (R.tree.layer J).card = S.card := by
  have hh := Set.ncard_range_of_injective (R.injective J)
  rw [R.bottom_image, Set.ncard_coe_finset, Nat.card_fin] at hh
  exact hh.symm

lemma HierarchyRestriction.fibre_card {J : ℕ} {T : TubeHierarchy J}
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S)
    (j : ℕ) (i : Fin (R.tree.layer J).card) :
    (leafFiber Finset.univ (R.tree.ancestor j) i).card =
      (leafFiber S (T.ancestor j) (R.map J i)).card := by
  classical
  have he : R.map J '' (leafFiber Finset.univ (R.tree.ancestor j) i :
      Set (Fin (R.tree.layer J).card)) =
      (leafFiber S (T.ancestor j) (R.map J i) : Set (Fin (T.layer J).card)) := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      have hae : R.tree.ancestor j a = R.tree.ancestor j i := by
        simpa only [Finset.mem_coe, leafFiber, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      have heq := congrArg (R.map j) hae
      rw [R.ancestor, R.ancestor] at heq
      simpa only [Finset.mem_coe, leafFiber, Finset.mem_filter] using And.intro (R.bottom_mem a) heq
    · intro hb
      have hb' : b ∈ S ∧ T.ancestor j b = T.ancestor j (R.map J i) := by
        simpa only [Finset.mem_coe, leafFiber, Finset.mem_filter] using hb
      have hbq : b ∈ Set.range (R.map J) := by rw [R.bottom_image]; exact hb'.1
      obtain ⟨a, rfl⟩ := hbq
      refine ⟨a, ?_, rfl⟩
      have hae : R.tree.ancestor j a = R.tree.ancestor j i := by
        apply R.injective j
        simpa only [R.ancestor] using hb'.2
      simpa only [Finset.mem_coe, leafFiber, Finset.mem_filter, Finset.mem_univ, true_and] using hae
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ (R.injective J), he,
    Set.ncard_coe_finset]

lemma HierarchyRestriction.balanced {J : ℕ} {T : TubeHierarchy J}
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S)
    {A : ℝ} {j : ℕ} (h : Balanced S (T.ancestor j) A) :
    Balanced Finset.univ (R.tree.ancestor j) A := by
  intro i hi k hk
  rw [R.fibre_card j i, R.fibre_card j k]
  exact h (R.map J i) (R.bottom_mem i) (R.map J k) (R.bottom_mem k)

lemma HierarchyRestriction.alignment {J : ℕ} {T : TubeHierarchy J}
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S)
    {u : Space} {h : ℝ} (H : HierarchyAlignment u h T) :
    HierarchyAlignment u h R.tree := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    simpa only [R.position, R.direction] using H.root (R.map 0 k)
  · intro j hj hjJ i
    simpa only [R.direction] using H.direction_cap j hj hjJ (R.map j i)
  · intro j hj hjJ i
    simpa only [R.position, R.direction] using H.aligned j hj hjJ (R.map j i)
  · intro j hj hjJ i
    simpa only [R.position, R.direction] using H.midpoint j hj hjJ (R.map j i)

lemma HierarchyRestriction.branch_retention {d θ g gap A lam : ℝ} {J : ℕ} {T : TubeHierarchy J}
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S)
    (H : HierarchyControl d θ g gap T) (hd : 0 ≤ d) (hA : 0 ≤ A) (hlam : 0 ≤ lam)
    (hbal : ∀ j, j ≤ J → Balanced S (T.ancestor j) A)
    (hcard : lam * (T.layer J).card ≤ S.card) {j : ℕ} (hj : j < J)
    (k : Fin (R.tree.layer j).card) :
    lam * {i | T.parent j i = R.map j k}.ncard ≤
      d ^ (-θ) * A * d ^ (-θ) * {i | R.tree.parent j i = k}.ncard := by
  classical
  obtain ⟨b, hb⟩ := R.tree.active j hj.le k
  let a := R.map J b
  have ha : a ∈ S := R.bottom_mem b
  have hak : T.ancestor j a = R.map j k := by rw [← R.ancestor, hb]
  have hret := balanced_branch_retention Finset.univ S (T.ancestor j) (T.ancestor (j + 1))
    (Finset.subset_univ S) (fun a b he => T.nested (by omega) (by omega) he)
    (Real.rpow_nonneg hd _) hA (Real.rpow_nonneg hd _) hlam
    (H.balanced j hj.le) (hbal j hj.le) (H.balanced (j + 1) (by omega))
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hcard) ha
  have hcold : {i | T.parent j i = R.map j k}.ncard =
      (branchFiber Finset.univ (T.ancestor j) (T.ancestor (j + 1)) a).card := by
    rw [← hak, ← T.branch_eq_fibre hj a, Set.ncard_coe_finset]
  rw [hcold, R.branches j hj k a ha hak]
  exact hret

/-- Geometry is preserved exactly; only the relative counting denominators need
a quantitative estimate when nodes are discarded. -/
theorem HierarchyRestriction.control {d θ θ' g gap : ℝ} {J : ℕ} {T : TubeHierarchy J}
    {S : Finset (Fin (T.layer J).card)} (R : HierarchyRestriction T S)
    (H : HierarchyControl d θ g gap T) (hd : 0 < d) (hd1 : d ≤ 1) (hθ : θ ≤ θ')
    (hbal : ∀ j, j ≤ J → Balanced S (T.ancestor j) (d ^ (-θ')))
    (hcount : ∀ j, j < J → ∀ k : Fin (R.tree.layer j).card,
      d ^ (-θ) * {i | T.parent j i = R.map j k}.ncard ≤
        d ^ (-θ') * {i | R.tree.parent j i = k}.ncard) :
    HierarchyControl d θ' g gap R.tree := by
  have hcoef : d ^ (-θ) ≤ d ^ (-θ') :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hθ)
  refine ⟨H.length_pos, by rw [R.radius, H.root_radius], ?_,
    by rw [R.radius, H.bottom_radius], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := Fintype.card_le_of_injective (R.map 0) (R.injective 0)
    have hc : (R.tree.layer 0).card ≤ 1 := by simpa only [Fintype.card_fin, H.root_card] using hh
    exact Nat.le_antisymm hc (R.tree.layer 0).card_pos
  · intro j hj
    simpa only [R.radius] using H.positive j hj
  · intro j hj
    simpa only [R.radius] using H.decreasing j hj
  · intro j hj
    simpa only [R.radius] using H.lower_gap j hj
  · intro j hj
    simpa only [R.radius] using H.upper_gap j hj
  · intro j hj i
    simpa only [R.radius, R.position, R.direction, R.parent j hj] using H.containment j hj (R.map (j + 1) i)
  · intro j hj i
    simpa only [R.radius, R.position, R.direction, R.parent j hj] using H.axis_buffer j hj (R.map (j + 1) i)
  · intro j hj k
    have hh := convexCount_reindex
      (WangZahlLot.Obl.wz_rescaled_fibre_alternatives.convexCount_mono hcoef (H.count j hj (R.map j k)))
      (R.map (j + 1)) (R.injective (j + 1))
      (Q := fun i => R.tree.parent j i = k)
      (fun i hi => (R.parent j hj i).symm.trans (congrArg (R.map j) hi))
    simpa only [Function.comp_def, R.radius, R.position, R.direction] using hh
  · intro j hj k
    have hh := slabBound_reindex (H.slab j hj (R.map j k))
      (R.map (j + 1)) (R.injective (j + 1))
      (Q := fun i => R.tree.parent j i = k)
      (fun i hi => (R.parent j hj i).symm.trans (congrArg (R.map j) hi)) (hcount j hj k)
    simpa only [Function.comp_def, R.radius, R.position, R.direction] using hh
  · intro j hj
    exact R.balanced (hbal j hj)

end WangZahlLot.Obl.wz_multiscale_finite_tower
