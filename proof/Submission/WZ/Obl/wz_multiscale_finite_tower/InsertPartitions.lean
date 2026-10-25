-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.InsertPartitions.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.PartitionHierarchy

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

def insertedLayer (k : ℕ) (M : Layer) (L : ℕ → Layer) (j : ℕ) : Layer :=
  if j ≤ k then L j else if j = k + 1 then M else L (j - 1)

noncomputable def insertedLabels {J : ℕ} (T : TubeHierarchy J) (k : ℕ) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (j : ℕ) :
    Fin (T.layer J).card → Fin (insertedLayer k M T.layer j).card := fun i =>
  ⟨if j ≤ k then (T.ancestor j i).val
    else if j = k + 1 then (a (T.ancestor (k + 1) i)).val else (T.ancestor (j - 1) i).val, by
    split_ifs with hj he
    · simpa only [insertedLayer, ite_eq_left hj] using (T.ancestor j i).isLt
    · simpa only [insertedLayer, ite_eq_right hj, ite_eq_left he] using (a (T.ancestor (k + 1) i)).isLt
    · simpa only [insertedLayer, ite_eq_right hj, ite_eq_right he] using (T.ancestor (j - 1) i).isLt⟩

lemma insertedLabels_full {J : ℕ} (T : TubeHierarchy J) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (ha : Function.Surjective a)
    (j : ℕ) (hj : j ≤ J + 1) : Function.Surjective (insertedLabels T k M a j) := by
  intro z
  by_cases hbefore : j ≤ k
  · let z' : Fin (T.layer j).card := ⟨z.val, by simpa only [insertedLayer, ite_eq_left hbefore] using z.isLt⟩
    obtain ⟨i, hi⟩ := T.active j (by omega) z'
    refine ⟨i, Fin.ext ?_⟩
    simpa only [insertedLabels, ite_eq_left hbefore] using congrArg Fin.val hi
  · by_cases he : j = k + 1
    · let z' : Fin M.card := ⟨z.val, by simpa only [insertedLayer, ite_eq_right hbefore, ite_eq_left he] using z.isLt⟩
      obtain ⟨i, hi⟩ := (ha.comp (T.active (k + 1) (by omega))) z'
      refine ⟨i, Fin.ext ?_⟩
      simpa only [insertedLabels, ite_eq_right hbefore, ite_eq_left he, Function.comp_apply] using congrArg Fin.val hi
    · let z' : Fin (T.layer (j - 1)).card :=
        ⟨z.val, by simpa only [insertedLayer, ite_eq_right hbefore, ite_eq_right he] using z.isLt⟩
      obtain ⟨i, hi⟩ := T.active (j - 1) (by omega) z'
      refine ⟨i, Fin.ext ?_⟩
      simpa only [insertedLabels, ite_eq_right hbefore, ite_eq_right he] using congrArg Fin.val hi

lemma insertedLabels_terminal {J : ℕ} (T : TubeHierarchy J) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) :
    Function.Bijective (insertedLabels T k M a (J + 1)) := by
  have hbefore : ¬J + 1 ≤ k := by omega
  have he : J + 1 ≠ k + 1 := by omega
  constructor
  · intro i i' hii'
    apply Fin.ext
    have hv := congrArg Fin.val hii'
    simp only [insertedLabels, ite_eq_right hbefore, ite_eq_right he] at hv
    rw [show J + 1 - 1 = J by omega, T.terminal] at hv
    exact hv
  · intro z
    let i : Fin (T.layer J).card :=
      ⟨z.val, by simpa only [insertedLayer, ite_eq_right hbefore, ite_eq_right he, Nat.add_sub_cancel] using z.isLt⟩
    refine ⟨i, Fin.ext ?_⟩
    simp only [insertedLabels, ite_eq_right hbefore, ite_eq_right he]
    change (T.ancestor J i).val = z.val
    rw [T.terminal]
    rfl

lemma insertedLabels_nested {J : ℕ} (T : TubeHierarchy J) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (b : Fin M.card → Fin (T.layer k).card)
    (hab : ∀ i, b (a i) = T.parent k i)
    (j : ℕ) (hj : j < J + 1) (i i' : Fin (T.layer J).card)
    (he : insertedLabels T k M a (j + 1) i = insertedLabels T k M a (j + 1) i') :
    insertedLabels T k M a j i = insertedLabels T k M a j i' := by
  have heval := congrArg Fin.val he
  apply Fin.ext
  by_cases hjk : j < k
  · have hjk' : j ≤ k := by omega
    have hjk1 : j + 1 ≤ k := by omega
    simp only [insertedLabels, ite_eq_left hjk1] at heval
    simp only [insertedLabels, ite_eq_left hjk']
    exact congrArg Fin.val (T.nested (by omega) (by omega) (Fin.ext heval))
  · by_cases hejk : j = k
    · subst j
      have hk1 : ¬k + 1 ≤ k := by omega
      simp only [insertedLabels, ite_eq_right hk1, ite_true] at heval
      simp only [insertedLabels, ite_eq_left (le_refl k)]
      have hh := congrArg b (Fin.ext heval)
      simpa only [hab, T.coherent k hk] using congrArg Fin.val hh
    · by_cases hejk1 : j = k + 1
      · subst j
        have hk1 : ¬k + 1 ≤ k := by omega
        have hk2 : ¬k + 1 + 1 ≤ k := by omega
        have hk2' : k + 1 + 1 ≠ k + 1 := by omega
        simp only [insertedLabels, ite_eq_right hk2, ite_eq_right hk2', Nat.add_sub_cancel] at heval
        simp only [insertedLabels, ite_eq_right hk1, ite_true]
        exact congrArg Fin.val (congrArg a (Fin.ext heval))
      · have hjk' : ¬j ≤ k := by omega
        have hjk1 : ¬j + 1 ≤ k := by omega
        have hne : j + 1 ≠ k + 1 := by omega
        simp only [insertedLabels, ite_eq_right hjk1, ite_eq_right hne, Nat.add_sub_cancel] at heval
        simp only [insertedLabels, ite_eq_right hjk', ite_eq_right hejk1]
        exact congrArg Fin.val (T.nested (by omega) (by omega) (Fin.ext heval))

/-- Insert one full intermediate partition between two consecutive layers. -/
noncomputable def insertHierarchy {J : ℕ} (T : TubeHierarchy J) {k : ℕ} (hk : k < J) (M : Layer)
    (a : Fin (T.layer (k + 1)).card → Fin M.card) (ha : Function.Surjective a)
    (b : Fin M.card → Fin (T.layer k).card) (hab : ∀ i, b (a i) = T.parent k i) : TubeHierarchy (J + 1) :=
  hierarchyOfPartitions (insertedLayer k M T.layer) (insertedLabels T k M a)
    (insertedLabels_terminal T hk M a) (insertedLabels_full T hk M a ha)
    (insertedLabels_nested T hk M a b hab)

end WangZahlLot.Obl.wz_multiscale_finite_tower
