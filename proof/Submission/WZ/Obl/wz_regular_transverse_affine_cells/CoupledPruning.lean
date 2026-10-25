-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.CoupledPruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Regularize

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

/-- Points with no incident pair satisfying a fixed relation. -/
def narrowRegion {n : ℕ} (R : Fin n → Fin n → Prop) (Y : Fin n → Set E) : Set E :=
  {p | ∀ i j, p ∈ Y i → p ∈ Y j → ¬R i j}

lemma narrowRegion_measurable {n : ℕ} (R : Fin n → Fin n → Prop)
    (Y : Fin n → Set E) (hY : ∀ i, MeasurableSet (Y i)) : MeasurableSet (narrowRegion R Y) := by
  classical
  have he : narrowRegion R Y = ⋂ i, ⋂ j, if R i j then (Y i ∩ Y j)ᶜ else Set.univ := by
    ext p
    simp only [narrowRegion, mem_ofPred_eq, mem_iInter]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro j
    split_ifs with h <;> simp [h]
  rw [he]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    by split_ifs; exacts [(hY i |>.inter (hY j)).compl, MeasurableSet.univ]

/-- Finite density pruning with simultaneous extraction of all narrow points.
The recorded narrow part is globally disjoint from the final broad core. -/
lemma coupled_density_pruning {n : ℕ} {κ : Type*}
    (R : Fin n → Fin n → Prop) (index : κ → Fin n) (region : κ → Set E)
    (cost : κ → ℝ≥0∞) (F : Finset κ) (hregion : ∀ t ∈ F, MeasurableSet (region t))
    (Y : Fin n → Set E) (hYm : ∀ i, MeasurableSet (Y i)) :
    ∃ H B : Fin n → Set E,
      (∀ i, MeasurableSet (H i)) ∧ (∀ i, MeasurableSet (B i)) ∧
      (∀ i, H i ⊆ Y i) ∧ (∀ i, B i ⊆ Y i) ∧
      Disjoint (⋃ i, H i) (⋃ i, B i) ∧
      (∀ p, (∃ i, p ∈ H i) → ∃ i j, p ∈ H i ∧ p ∈ H j ∧ R i j) ∧
      (∀ p i j, p ∈ B i → p ∈ B j → ¬R i j) ∧
      (∑ i, volume (Y i)) ≤ (∑ i, volume (H i)) + (∑ i, volume (B i)) + ∑ t ∈ F, cost t ∧
      ∀ t ∈ F, (H (index t) ∩ region t).Nonempty →
        cost t ≤ volume (H (index t) ∩ region t) := by
  classical
  induction F using Finset.strongInductionOn generalizing Y with
  | _ F ih =>
    let N := narrowRegion R Y
    let B₀ : Fin n → Set E := fun i => Y i ∩ N
    let Z : Fin n → Set E := fun i => Y i \ N
    have hNm : MeasurableSet N := narrowRegion_measurable R Y hYm
    have hB₀m : ∀ i, MeasurableSet (B₀ i) := fun i => (hYm i).inter hNm
    have hZm : ∀ i, MeasurableSet (Z i) := fun i => (hYm i).diff hNm
    have hZsub : ∀ i, Z i ⊆ Y i := fun _ => sdiff_subset
    have hB₀sub : ∀ i, B₀ i ⊆ Y i := fun _ => inter_subset_left
    have hB₀N : ∀ i, B₀ i ⊆ N := fun _ => inter_subset_right
    have hZN : ∀ i, Z i ⊆ Nᶜ := fun _ => sdiff_subset_compl _ _
    have hZdisj : Disjoint (⋃ i, Z i) (⋃ i, B₀ i) :=
      disjoint_compl_left.mono (iUnion_subset hZN) (iUnion_subset hB₀N)
    have hZbroad : ∀ p, (∃ i, p ∈ Z i) → ∃ i j, p ∈ Z i ∧ p ∈ Z j ∧ R i j := by
      intro p hp
      obtain ⟨k, hpk⟩ := hp
      have hn : ¬∀ i j, p ∈ Y i → p ∈ Y j → ¬R i j := hpk.2
      push Not at hn
      obtain ⟨i, j, hi, hj, hR⟩ := hn
      exact ⟨i, j, ⟨hi, hpk.2⟩, ⟨hj, hpk.2⟩, hR⟩
    have hB₀narrow : ∀ p i j, p ∈ B₀ i → p ∈ B₀ j → ¬R i j := by
      intro p i j hi hj
      exact hi.2 i j hi.1 hj.1
    have hsplit : (∑ i, volume (Y i)) = (∑ i, volume (Z i)) + ∑ i, volume (B₀ i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (measure_sdiff_add_inter (Y i) hNm).symm
    by_cases hgood : ∀ t ∈ F, (Z (index t) ∩ region t).Nonempty →
        cost t ≤ volume (Z (index t) ∩ region t)
    · refine ⟨Z, B₀, hZm, hB₀m, hZsub, hB₀sub, hZdisj, hZbroad, hB₀narrow, ?_, hgood⟩
      rw [hsplit]
      exact le_self_add
    push Not at hgood
    obtain ⟨t, ht, _hmeet, hsmall⟩ := hgood
    let Z' : Fin n → Set E := Function.update Z (index t) (Z (index t) \ region t)
    have hZ'm : ∀ i, MeasurableSet (Z' i) := by
      intro i
      by_cases hi : i = index t
      · subst i
        simpa only [Z', Function.update_self] using (hZm (index t)).diff (hregion t ht)
      · simpa only [Z', Function.update_of_ne hi] using hZm i
    have hZ'sub : ∀ i, Z' i ⊆ Z i := by
      intro i
      by_cases hi : i = index t
      · subst i
        simpa only [Z', Function.update_self] using (sdiff_subset : Z (index t) \ region t ⊆ Z (index t))
      · simp only [Z', Function.update_of_ne hi, subset_rfl]
    have hregion' : ∀ u ∈ F.erase t, MeasurableSet (region u) :=
      fun u hu => hregion u (Finset.mem_of_mem_erase hu)
    obtain ⟨H, B', hHm, hB'm, hHZ', hB'Z', hHB', hHbroad, hB'narrow, hmass, hreg⟩ :=
      ih (F.erase t) (Finset.erase_ssubset ht) hregion' Z' hZ'm
    let B : Fin n → Set E := fun i => B₀ i ∪ B' i
    have hHN : ∀ i, H i ⊆ Nᶜ := fun i => (hHZ' i).trans ((hZ'sub i).trans (hZN i))
    have hB'N : ∀ i, B' i ⊆ Nᶜ := fun i => (hB'Z' i).trans ((hZ'sub i).trans (hZN i))
    have hBBdisj : ∀ i, Disjoint (B₀ i) (B' i) :=
      fun i => disjoint_compl_right.mono (hB₀N i) (hB'N i)
    have hBmass : (∑ i, volume (B i)) = (∑ i, volume (B₀ i)) + ∑ i, volume (B' i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact measure_union (hBBdisj i) (hB'm i)
    refine ⟨H, B, hHm, fun i => (hB₀m i).union (hB'm i),
      fun i => (hHZ' i).trans ((hZ'sub i).trans (hZsub i)),
      fun i => union_subset (hB₀sub i) ((hB'Z' i).trans ((hZ'sub i).trans (hZsub i))),
      ?_, hHbroad, ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro p hp hpB
      obtain ⟨i, hi⟩ := mem_iUnion.mp hpB
      rcases hi with hi | hi
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hp
        exact (hHN j hj) (hB₀N i hi)
      · exact Set.disjoint_left.mp hHB' hp (mem_iUnion.mpr ⟨i, hi⟩)
    · intro p i j hi hj
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact hB₀narrow p i j hi hj
      · exact False.elim ((hB'N j hj) (hB₀N i hi))
      · exact False.elim ((hB'N i hi) (hB₀N j hj))
      · exact hB'narrow p i j hi hj
    · have hdelete : (∑ i, volume (Z i)) ≤ (∑ i, volume (Z' i)) + cost t := by
        calc (∑ i, volume (Z i)) ≤ ∑ i, (volume (Z' i) + if i = index t then cost t else 0) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hi : i = index t
              · subst i
                simp only [Z', Function.update_self, ite_eq_left]
                calc volume (Z (index t)) = volume (Z (index t) \ region t) +
                    volume (Z (index t) ∩ region t) := (measure_sdiff_add_inter _ (hregion t ht)).symm
                  _ ≤ _ := add_le_add le_rfl hsmall.le
              · simp only [Z', Function.update_of_ne hi, ite_eq_right hi, add_zero, le_refl]
          _ = _ := by rw [Finset.sum_add_distrib]; simp
      rw [hsplit, hBmass]
      calc (∑ i, volume (Z i)) + ∑ i, volume (B₀ i)
          ≤ ((∑ i, volume (H i)) + (∑ i, volume (B' i)) + ∑ u ∈ F.erase t, cost u) +
            cost t + ∑ i, volume (B₀ i) :=
              add_le_add (hdelete.trans (add_le_add hmass le_rfl)) le_rfl
        _ = _ := by rw [← add_assoc, add_assoc (_ + _) (∑ u ∈ F.erase t, cost u),
            Finset.sum_erase_add _ _ ht]; ring
    · intro u hu hmeet
      by_cases hut : u = t
      · subst u
        obtain ⟨p, hp, hpt⟩ := hmeet
        have hp' : p ∈ Z (index t) \ region t := by
          simpa only [Z', Function.update_self] using hHZ' _ hp
        exact False.elim (hp'.2 hpt)
      · exact hreg u (Finset.mem_erase.mpr ⟨hut, hu⟩) hmeet

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
