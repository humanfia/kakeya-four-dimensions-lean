-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CellPieceAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.SeparatedCellGlue

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set Metric
open scoped Classical

set_option maxHeartbeats 1000000 in
/-- Assemble finitely many local packet families with tube-wise separation.
All mass and average-density sums are exact, and triggered geometric facts
survive the union of the shadings. -/
theorem assemble_separated_cell_pieces {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) {r : ℝ} (hr : 0 < r) {n N : ℕ}
    (Y : Fin n → Set X) (C : Fin N → Set X) (q : Fin N → X)
    (F : Fin N → Finset X) (V : Fin N → Fin n → Set X)
    (H P : Fin N → X → Set X) (Q : Fin n → Fin N → X → Prop)
    (hCdisj : Pairwise fun j k => Disjoint (C j) (C k))
    (hV : ∀ j i, MeasurableSet (V j i) ∧ V j i ⊆ Y i ∩ C j)
    (hVball : ∀ j i, V j i ⊆ ball (q j) r)
    (hsep : ∀ i j k, j ≠ k → (V j i).Nonempty → (V k i).Nonempty →
      10 * r < dist (q j) (q k))
    (hHdisj : ∀ j, (↑(F j) : Set X).PairwiseDisjoint (H j))
    (hHunion : ∀ j, (⋃ z ∈ F j, H j z) = ⋃ i, V j i)
    (hP : ∀ j z, z ∈ F j → P j z ⊆ ball (q j) (3 * r))
    (hlocal : ∀ j z, z ∈ F j → ∀ i, (V j i ∩ H j z).Nonempty →
      V j i ∩ P j z ⊆ H j z ∧ Q i j z)
    {a b : ENNReal}
    (hkeep : a * (∑ i, μ (Y i)) ≤ ∑ j, ∑ i, μ (V j i))
    (hdense : ∀ j, b * (F j).card ≤ ∑ z ∈ F j, μ (H j z)) :
    ∃ (L : ℕ) (cell : Fin L → Fin N) (z : Fin L → X) (Z : Fin n → Set X),
      (∀ l, z l ∈ F (cell l)) ∧
      (∀ i, Z i = ⋃ j, V j i) ∧
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (∑ i, μ (Z i)) = ∑ j, ∑ i, μ (V j i) ∧
      (Pairwise fun l k => Disjoint (H (cell l) (z l)) (H (cell k) (z k))) ∧
      (⋃ l, H (cell l) (z l)) = ⋃ i, Z i ∧
      a * (∑ i, μ (Y i)) ≤ ∑ i, μ (Z i) ∧
      b * L ≤ ∑ l, μ (H (cell l) (z l)) ∧
      ∀ i l, (Z i ∩ H (cell l) (z l)).Nonempty →
        Z i ∩ P (cell l) (z l) ⊆ H (cell l) (z l) ∧ Q i (cell l) (z l) := by
  let S := Finset.univ.sigma F
  let e : Fin S.card → (j : Fin N) × X := fun l => (S.equivFin.symm l).val
  have heinj : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have hemem (l : Fin S.card) : e l ∈ S := (S.equivFin.symm l).property
  have heF (l : Fin S.card) : (e l).2 ∈ F (e l).1 := (Finset.mem_sigma.mp (hemem l)).2
  have hesurj (s) (hs : s ∈ S) : ∃ l, e l = s :=
    ⟨S.equivFin ⟨s, hs⟩, by simp [e]⟩
  have hsum (f : Fin N → X → ENNReal) :
      (∑ l, f (e l).1 (e l).2) = ∑ j, ∑ z ∈ F j, f j z := by
    calc
      _ = ∑ s ∈ S, f s.1 s.2 := by
        rw [Equiv.sum_comp S.equivFin.symm (fun s : S => f s.val.1 s.val.2)]
        exact Finset.sum_coe_sort S (fun s => f s.1 s.2)
      _ = _ := Finset.sum_sigma Finset.univ F (fun (s : (j : Fin N) × X) => f s.1 s.2)
  have hHC (j : Fin N) (z : X) (hz : z ∈ F j) : H j z ⊆ C j := by
    intro p hp
    have hp' : p ∈ ⋃ i, V j i := hHunion j ▸ mem_iUnion₂.mpr ⟨z, hz, hp⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp'
    exact ((hV j i).2 hi).2
  let Z : Fin n → Set X := fun i => ⋃ j, V j i
  have hZ (i : Fin n) : MeasurableSet (Z i) ∧ Z i ⊆ Y i :=
    ⟨MeasurableSet.iUnion (fun j => (hV j i).1),
      iUnion_subset (fun j => (hV j i).2.trans inter_subset_left)⟩
  have hZmass (i : Fin n) : μ (Z i) = ∑ j, μ (V j i) := by
    have hh := measure_iUnion (fun j k hjk => (hCdisj hjk).mono
      ((hV j i).2.trans inter_subset_right) ((hV k i).2.trans inter_subset_right))
      (fun j => (hV j i).1) (μ := μ)
    rw [tsum_fintype] at hh
    exact hh
  have haccount : (∑ i, μ (Z i)) = ∑ j, ∑ i, μ (V j i) := by
    simp_rw [hZmass]
    exact Finset.sum_comm
  refine ⟨S.card, (fun l => (e l).1), (fun l => (e l).2), Z, heF,
    fun _ => rfl, hZ, haccount, ?_, ?_, ?_, ?_, ?_⟩
  · intro l k hlk
    by_cases hj : (e l).1 = (e k).1
    · have hz : (e l).2 ≠ (e k).2 := by
        intro hh
        exact hlk (heinj (Sigma.ext hj (heq_of_eq hh)))
      have hh := hHdisj (e l).1 (heF l) (hj.symm ▸ heF k) hz
      simpa only [hj] using hh
    · exact (hCdisj hj).mono (hHC _ _ (heF l)) (hHC _ _ (heF k))
  · calc
      (⋃ l, H (e l).1 (e l).2) = ⋃ j, ⋃ z ∈ F j, H j z := by
        apply subset_antisymm
        · intro p hp
          obtain ⟨l, hl⟩ := mem_iUnion.mp hp
          exact mem_iUnion.mpr ⟨(e l).1, mem_iUnion₂.mpr ⟨(e l).2, heF l, hl⟩⟩
        · intro p hp
          obtain ⟨j, hj⟩ := mem_iUnion.mp hp
          obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hj
          obtain ⟨l, hl⟩ := hesurj ⟨j, z⟩ (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hz⟩)
          exact mem_iUnion.mpr ⟨l, by simpa only [hl] using hpz⟩
      _ = ⋃ j, ⋃ i, V j i := by simp only [hHunion]
      _ = ⋃ i, Z i := iUnion_comm V
  · exact hkeep.trans_eq haccount.symm
  · have hcard : (S.card : ENNReal) = ∑ j : Fin N, ((F j).card : ENNReal) := by
      dsimp only [S]
      rw [Finset.card_sigma, Nat.cast_sum]
    change b * S.card ≤ ∑ l, μ (H (e l).1 (e l).2)
    rw [hcard, Finset.mul_sum, hsum (fun j z => μ (H j z))]
    exact Finset.sum_le_sum (fun j _ => hdense j)
  · intro i l hi
    have hlocalmeet : (V (e l).1 i ∩ H (e l).1 (e l).2).Nonempty := by
      simpa only [Z, disjoint_cells_union_inter C (fun j => V j i) hCdisj
        (fun j => (hV j i).2.trans inter_subset_right) _ (hHC _ _ (heF l))] using hi
    refine ⟨?_, (hlocal _ _ (heF l) i hlocalmeet).2⟩
    exact separated_cells_triggered_containment hr C q V hCdisj
      (fun j i => (hV j i).2.trans inter_subset_right) hVball hsep (e l).1
      (H (e l).1 (e l).2) (P (e l).1 (e l).2) (hHC _ _ (heF l)) (hP _ _ (heF l))
      (fun i hi => (hlocal _ _ (heF l) i hi).1) i hi

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
