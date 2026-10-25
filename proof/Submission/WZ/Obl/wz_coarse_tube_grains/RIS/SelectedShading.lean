-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SelectedShading.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FiberMultiplicity

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SelectedShading

open MeasureTheory Set
open scoped Classical

noncomputable abbrev enum {n : ℕ} (Q : Finset (Fin n)) (j : Fin Q.card) : Fin n :=
  (Q.equivFin.symm j).val

theorem enum_mem {n : ℕ} (Q : Finset (Fin n)) (j : Fin Q.card) : enum Q j ∈ Q :=
  (Q.equivFin.symm j).property

theorem enum_back {n : ℕ} (Q : Finset (Fin n)) (i : Fin n) (hi : i ∈ Q) :
    enum Q (Q.equivFin ⟨i, hi⟩) = i := by simp [enum]

noncomputable def lift {n : ℕ} {X : Type*} (Q : Finset (Fin n))
    (Z : Fin Q.card → Set X) (i : Fin n) : Set X :=
  if hi : i ∈ Q then Z (Q.equivFin ⟨i, hi⟩) else ∅

theorem lift_enum {n : ℕ} {X : Type*} (Q : Finset (Fin n))
    (Z : Fin Q.card → Set X) (j : Fin Q.card) : lift Q Z (enum Q j) = Z j := by
  dsimp only [lift]
  rw [dif_pos (enum_mem Q j)]
  congr 1
  change Q.equivFin ⟨(Q.equivFin.symm j).val, _⟩ = j
  simp

theorem lift_zero {n : ℕ} {X : Type*} (Q : Finset (Fin n))
    (Z : Fin Q.card → Set X) (i : Fin n) (hi : i ∉ Q) : lift Q Z i = ∅ := by
  simp only [lift, dif_neg hi]

theorem count_enum {n : ℕ} (Q : Finset (Fin n)) (R : Fin n → Prop)
    (hR : ∀ i, R i → i ∈ Q) : {j | R (enum Q j)}.ncard = {i | R i}.ncard := by
  change {j | R ((Q.equivFin.symm j).val)}.ncard = _
  rw [ncard_comp_equivFin]
  congr 1
  ext i
  exact ⟨And.right, fun hi => ⟨hR i hi, hi⟩⟩

theorem sum_enum {n : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Q : Finset (Fin n)) (U : Fin n → Set X)
    (hU : ∀ i, i ∉ Q → U i = ∅) :
    (∑ j, μ (U (enum Q j))) = ∑ i, μ (U i) := by
  have hs := sum_comp_equivFin Q (fun i => μ (U i))
  change (∑ j, μ (U (enum Q j))) = _ at hs
  rw [hs]
  exact Finset.sum_subset (Finset.subset_univ Q) (fun i _ hi => by rw [hU i hi, measure_empty])

theorem union_enum {n : ℕ} {X : Type*} (Q : Finset (Fin n)) (U : Fin n → Set X)
    (hU : ∀ i, i ∉ Q → U i = ∅) : (⋃ j, U (enum Q j)) = ⋃ i, U i := by
  apply subset_antisymm
  · exact iUnion_mono' fun j => ⟨enum Q j, subset_rfl⟩
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    have hiQ : i ∈ Q := by
      by_contra hh
      rw [hU i hh] at hi
      exact hi.elim
    exact mem_iUnion.mpr ⟨Q.equivFin ⟨i, hiQ⟩, by simpa only [enum_back] using hi⟩

theorem sum_lift {n : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Q : Finset (Fin n)) (Z : Fin Q.card → Set X) :
    (∑ i, μ (lift Q Z i)) = ∑ j, μ (Z j) := by
  simpa only [lift_enum] using (sum_enum μ Q (lift Q Z) (lift_zero Q Z)).symm

theorem union_lift {n : ℕ} {X : Type*} (Q : Finset (Fin n))
    (Z : Fin Q.card → Set X) : (⋃ i, lift Q Z i) = ⋃ j, Z j := by
  simpa only [lift_enum] using (union_enum Q (lift Q Z) (lift_zero Q Z)).symm

theorem card_lift {n : ℕ} {X : Type*} (Q : Finset (Fin n))
    (Z : Fin Q.card → Set X) (p : X) :
    (Finset.univ.filter fun i => p ∈ lift Q Z i).card =
      (Finset.univ.filter fun j => p ∈ Z j).card := by
  have hh := count_enum Q (fun i => p ∈ lift Q Z i) (fun i hi => by
    by_contra hn
    rw [lift_zero Q Z i hn] at hi
    exact hi.elim)
  simp only [lift_enum] at hh
  have hcard {m : ℕ} (U : Fin m → Set X) :
      {i | p ∈ U i}.ncard = (Finset.univ.filter fun i => p ∈ U i).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  simpa only [hcard] using hh.symm

theorem lift_refines {n : ℕ} {X : Type*} [MeasurableSpace X]
    (Q : Finset (Fin n)) (Y : Fin n → Set X) (Z : Fin Q.card → Set X)
    (hZ : ∀ j, MeasurableSet (Z j) ∧ Z j ⊆ Y (enum Q j)) :
    ∀ i, MeasurableSet (lift Q Z i) ∧ lift Q Z i ⊆ Y i := by
  intro i
  by_cases hi : i ∈ Q
  · have hh := hZ (Q.equivFin ⟨i, hi⟩)
    simpa only [lift, dif_pos hi, enum_back] using hh
  · rw [lift_zero Q Z i hi]
    exact ⟨MeasurableSet.empty, empty_subset _⟩

theorem lift_nonempty {n : ℕ} {X : Type*} (Q : Finset (Fin n))
    (Z : Fin Q.card → Set X) {i : Fin n} (hi : (lift Q Z i).Nonempty) :
    ∃ j, enum Q j = i ∧ (Z j).Nonempty := by
  have hiQ : i ∈ Q := by
    by_contra hn
    rw [lift_zero Q Z i hn] at hi
    exact Set.not_nonempty_empty hi
  refine ⟨Q.equivFin ⟨i, hiQ⟩, enum_back Q i hiQ, ?_⟩
  simpa only [lift, dif_pos hiQ] using hi

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SelectedShading
