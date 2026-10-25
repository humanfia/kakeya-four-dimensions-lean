-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GroupedRegularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.GroupedSelection
import Submission.WZ.Obl.wz_multiscale_finite_tower.InsertControl

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)

theorem GroupedSelection.regularize {J k : ℕ} {T : TubeHierarchy J}
    {H B R R' : ℝ} (G : GroupedSelection (T.parent k) H B) (hk : k < J)
    (hbal : ∀ j, j ≤ J → Balanced Finset.univ (T.ancestor j) R)
    (q : ℕ) (hq : 0 < q) (hR' : 1 < R')
    (hn : ((T.layer J).card : ℝ) < R' ^ q)
    (hU : (Finset.univ.filter (fun i => T.ancestor (k + 1) i ∈ G.selected)).Nonempty) :
    ∃ S : Finset (Fin (T.layer J).card),
      S ⊆ Finset.univ.filter (fun i => T.ancestor (k + 1) i ∈ G.selected) ∧ S.Nonempty ∧
      ((Finset.univ.filter (fun i => T.ancestor (k + 1) i ∈ G.selected)).card : ℝ) ≤
        (q : ℝ) ^ (k + 2) * S.card ∧
      (∀ j, j ≤ J → Balanced S (T.ancestor j) (max R R')) ∧
      Balanced S (G.group ∘ T.ancestor (k + 1)) R' ∧
      ∀ i, T.ancestor (k + 1) i ∈ G.selected → ∀ i', T.ancestor (k + 1) i' ∈ G.selected →
        G.group (T.ancestor (k + 1) i) = G.group (T.ancestor (k + 1) i') → (i ∈ S ↔ i' ∈ S) := by
  classical
  let c := G.group ∘ T.ancestor (k + 1)
  let p : ℕ → Fin (T.layer J).card → ℕ := fun j i =>
    if j ≤ k then (T.ancestor j i).val else (c i).val
  let U := Finset.univ.filter (fun i => T.ancestor (k + 1) i ∈ G.selected)
  have hcoarse {i i' : Fin (T.layer J).card} (he : c i = c i') :
      T.ancestor k i = T.ancestor k i' := by
    have hh := congrArg (T.parent k) he
    simpa only [c, Function.comp_apply, G.parent_group, T.coherent k hk] using hh
  have hnested (a b : ℕ) (hab : a ≤ b) (hb : b < k + 2)
      (i i' : Fin (T.layer J).card) (he : p b i = p b i') : p a i = p a i' := by
    by_cases hbk : b ≤ k
    · have hak : a ≤ k := hab.trans hbk
      simp only [p, ite_eq_left hbk] at he
      simp only [p, ite_eq_left hak]
      exact congrArg Fin.val (T.nested hab (by omega) (Fin.ext he))
    · simp only [p, ite_eq_right hbk] at he
      by_cases hak : a ≤ k
      · simp only [p, ite_eq_left hak]
        exact congrArg Fin.val (T.nested hak hk.le (hcoarse (Fin.ext he)))
      · simpa only [p, ite_eq_right hak] using he
  have hpc (a : ℕ) (ha : a < k + 2) (i i' : Fin (T.layer J).card)
      (he : c i = c i') : p a i = p a i' := by
    by_cases hak : a ≤ k
    · simp only [p, ite_eq_left hak]
      exact congrArg Fin.val (T.nested hak hk.le (hcoarse he))
    · simpa only [p, ite_eq_right hak] using congrArg Fin.val he
  obtain ⟨color, hcolor⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.exists_size_color
    (T.layer J).card q R' hq hR' hn
  obtain ⟨S, hSU, hmass, hSbal, hclosed⟩ := regularize_nested_closed p c (k + 2) q
    (T.layer J).card hq R' color hcolor hnested hpc U
    (by simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ U) (fun _ => 1)
  have hcard : (U.card : ℝ) ≤ (q : ℝ) ^ (k + 2) * S.card := by
    have hh : (U.card : ENNReal) ≤ (q : ENNReal) ^ (k + 2) * S.card := by simpa using hmass
    exact_mod_cast hh
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have he : S.card = 0 := by omega
    rw [he, Nat.cast_zero, mul_zero] at hcard
    exact (not_le_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hU) : (0 : ℝ) < U.card)) hcard
  have hclose (i) (hi : T.ancestor (k + 1) i ∈ G.selected)
      (i') (hi' : T.ancestor (k + 1) i' ∈ G.selected) (he : c i = c i') :
      (i ∈ S ↔ i' ∈ S) := hclosed i (by simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
        i' (by simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi') he
  refine ⟨S, hSU, hS, hcard, ?_, ?_, hclose⟩
  · intro j hj
    by_cases hjk : j ≤ k
    · have he : p j = Fin.val ∘ T.ancestor j := by
        funext i
        simp only [p, ite_eq_left hjk, Function.comp_apply]
      have hh := hSbal j (by omega)
      rw [he] at hh
      exact balanced_mono ((balanced_postcomp_iff S _ Fin.val Fin.val_injective R').mp hh)
        (le_max_right _ _)
    · apply balanced_mono (balanced_of_closed S (T.ancestor j) ?_ (hbal j hj)) (le_max_left _ _)
      intro i hi i' he
      have hchild : T.ancestor (k + 1) i' = T.ancestor (k + 1) i :=
        T.nested (by omega) hj he
      have hiU : T.ancestor (k + 1) i ∈ G.selected := (Finset.mem_filter.mp (hSU hi)).2
      have hi'U : T.ancestor (k + 1) i' ∈ G.selected := by rwa [hchild]
      exact (hclose i hiU i' hi'U (congrArg G.group hchild.symm)).mp hi
  · have he : p (k + 1) = Fin.val ∘ c := by
      funext i
      simp only [p, ite_eq_right (show ¬ k + 1 ≤ k by omega), Function.comp_apply]
    have hh := hSbal (k + 1) (by omega)
    rw [he] at hh
    exact (balanced_postcomp_iff S c Fin.val Fin.val_injective R').mp hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
