-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Reindex.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Basic
import Submission.WZ.Obl.wz_tower_balanced_refinement.Reindex

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

lemma reindex_whole_fibres {m N : ℕ} (S S' : Finset (Fin m)) (hS : S' ⊆ S)
    (hS' : S'.Nonempty) (f : Fin m → Fin N)
    (hwhole : ∀ i ∈ S', ∀ j ∈ S, f i = f j → j ∈ S') :
    ∃ (N' : ℕ) (b : Fin N' → Fin N) (g : Fin m → Fin N') (rep : Fin N' → Fin m),
      0 < N' ∧ Function.Injective b ∧ (∀ k, rep k ∈ S' ∧ f (rep k) = b k) ∧
      (∀ i ∈ S', b (g i) = f i) ∧
      (∀ k i, (i ∈ S' ∧ g i = k) ↔ (i ∈ S ∧ f i = b k)) := by
  classical
  let C := S'.image f
  have hC : C.Nonempty := hS'.image f
  have hCpos : 0 < C.card := Finset.card_pos.mpr hC
  let b := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate C
  have hbinj : Function.Injective b := WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_injective C
  have hreps (k : Fin C.card) : ∃ i, i ∈ S' ∧ f i = b k :=
    Finset.mem_image.mp (WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate_mem C k)
  choose rep hrep using hreps
  let g : Fin m → Fin C.card := fun i => if h : f i ∈ C then
    Finset.equivFin C ⟨f i, h⟩ else ⟨0, hCpos⟩
  have hgb (i) (hi : i ∈ S') : b (g i) = f i := by
    have hfi : f i ∈ C := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    simp [g, hfi, b, WangZahlLot.Obl.wz_tower_balanced_refinement.enumerate]
  refine ⟨C.card, b, g, rep, hCpos, hbinj, hrep, hgb, ?_⟩
  intro k i
  constructor
  · rintro ⟨hi, hik⟩
    exact ⟨hS hi, by rw [← hgb i hi, hik]⟩
  · rintro ⟨hi, hfi⟩
    have hi' := hwhole (rep k) (hrep k).1 i hi ((hrep k).2.trans hfi.symm)
    exact ⟨hi', hbinj ((hgb i hi').trans hfi)⟩

lemma slabBound_embedding {m n : ℕ} (j : Fin m → Fin n) (hj : Function.Injective j)
    {P : Fin m → Prop} {Q : Fin n → Prop} {U : Fin n → Set Space} {D : Set Space} {L : ℝ}
    (hQ : ∀ k, Q k ↔ ∃ i, P i ∧ j i = k)
    (h : SlabBound D L P (fun i => U (j i))) : SlabBound D L Q U := by
  have hcard (R : Fin n → Prop) : {k | Q k ∧ R k}.ncard = {i | P i ∧ R (j i)}.ncard := by
    have he : {k | Q k ∧ R k} = j '' {i | P i ∧ R (j i)} := by
      ext k
      constructor
      · rintro ⟨hk, hR⟩
        obtain ⟨i, hi, rfl⟩ := (hQ k).mp hk
        exact ⟨i, ⟨hi, hR⟩, rfl⟩
      · rintro ⟨i, ⟨hi, hR⟩, rfl⟩
        exact ⟨(hQ (j i)).mpr ⟨i, hi, rfl⟩, hR⟩
    rw [he, Set.ncard_image_of_injective _ hj]
  intro u t r hu hr
  have hbase : {k | Q k}.ncard = {i | P i}.ncard := by
    simpa only [and_true] using hcard (fun _ => True)
  rw [hcard, hbase]
  exact h u t r hu hr

/-- Extend shadings and an assignment along an injective finite selection. -/
lemma extend_selection {m n N : ℕ} (hm : 0 < m) (j : Fin m → Fin n) (hj : Function.Injective j)
    (S : Finset (Fin m)) (g : Fin m → Fin N) (Y : Fin n → Set Space)
    (Z : Fin m → Set Space) (hZ : ∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y (j i)) :
    ∃ (S' : Finset (Fin n)) (Z' : Fin n → Set Space) (g' : Fin n → Fin N),
      (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Y i) ∧
      (∑ i ∈ S', volume (Z' i)) = ∑ i ∈ S, volume (Z i) ∧
      (∀ k i, (i ∈ S' ∧ g' i = k) ↔ ∃ a, a ∈ S ∧ g a = k ∧ j a = i) ∧
      (∀ i ∈ S', ∃ a, a ∈ S ∧ j a = i ∧ g' i = g a) := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let inv := Function.invFun j
  have hinv : ∀ a, inv (j a) = a := Function.leftInverse_invFun hj
  let Z' := fun i => if i ∈ Set.range j then Z (inv i) else ∅
  let g' := fun i => g (inv i)
  have hZeq (a) : Z' (j a) = Z a := by simp only [Z', Set.mem_range_self, if_true, hinv]
  refine ⟨S.image j, Z', g', ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ Set.range j
    · obtain ⟨a, rfl⟩ := hi
      rw [hZeq]
      exact hZ a
    · simp only [Z', if_neg hi]
      exact ⟨MeasurableSet.empty, empty_subset _⟩
  · rw [Finset.sum_image (fun a _ b _ hab => hj hab)]
    apply Finset.sum_congr rfl
    intro a _
    rw [hZeq]
  · intro k i
    constructor
    · rintro ⟨hi, hik⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨a, ha, by simpa only [g', hinv] using hik, rfl⟩
    · rintro ⟨a, ha, hag, rfl⟩
      exact ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, by simpa only [g', hinv] using hag⟩
  · intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨a, ha, rfl, by simp only [g', hinv]⟩

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
