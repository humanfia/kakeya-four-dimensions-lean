-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.UniformCellAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CellPieceAssembly
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CellLevelSelection

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set Metric
open scoped Classical

set_option maxHeartbeats 1000000 in
/-- Select whole packets with a common local level and assemble them into
one uniformly shaded family. Piece density and triggered geometry survive
unchanged; mass retention costs only the number of possible dyadic levels. -/
theorem assemble_uniform_cell_pieces {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) {r : ℝ} (hr : 0 < r) {n N : ℕ}
    (Y : Fin n → Set X) (C : Fin N → Set X) (q : Fin N → X)
    (F : Fin N → Finset X) (V : Fin N → Fin n → Set X)
    (H P : Fin N → X → Set X) (Q : Fin n → Fin N → X → Prop) (k : Fin N → ℕ)
    (hCdisj : Pairwise fun j l => Disjoint (C j) (C l))
    (hV : ∀ j i, MeasurableSet (V j i) ∧ V j i ⊆ Y i ∩ C j)
    (hVball : ∀ j i, V j i ⊆ ball (q j) r)
    (hsep : ∀ i j l, j ≠ l → (V j i).Nonempty → (V l i).Nonempty →
      10 * r < dist (q j) (q l))
    (hHdisj : ∀ j, (↑(F j) : Set X).PairwiseDisjoint (H j))
    (hHunion : ∀ j, (⋃ z ∈ F j, H j z) = ⋃ i, V j i)
    (hP : ∀ j z, z ∈ F j → P j z ⊆ ball (q j) (3 * r))
    (hlocal : ∀ j z, z ∈ F j → ∀ i, (V j i ∩ H j z).Nonempty →
      V j i ∩ P j z ⊆ H j z ∧ Q i j z)
    (hlevel : ∀ j p, p ∈ ⋃ i, V j i →
      2 ^ k j ≤ (Finset.univ.filter fun i => p ∈ V j i).card ∧
        (Finset.univ.filter fun i => p ∈ V j i).card < 2 ^ (k j + 1))
    {a b : ENNReal}
    (hkeep : a * (∑ i, μ (Y i)) ≤ ∑ j, ∑ i, μ (V j i))
    (hdense : ∀ j, b * (F j).card ≤ ∑ z ∈ F j, μ (H j z)) :
    ∃ (m L : ℕ) (cell : Fin L → Fin N) (z : Fin L → X) (Z : Fin n → Set X),
      m ≤ Nat.log 2 n ∧ (∀ l, z l ∈ F (cell l)) ∧
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (Pairwise fun l j => Disjoint (H (cell l) (z l)) (H (cell j) (z j))) ∧
      (⋃ l, H (cell l) (z l)) = ⋃ i, Z i ∧
      a * (∑ i, μ (Y i)) ≤ (Nat.log 2 n + 1 : ℕ) * ∑ i, μ (Z i) ∧
      b * L ≤ ∑ l, μ (H (cell l) (z l)) ∧
      (∀ i l, (Z i ∩ H (cell l) (z l)).Nonempty →
        Z i ∩ P (cell l) (z l) ⊆ H (cell l) (z l) ∧ Q i (cell l) (z l)) ∧
      ∀ p ∈ ⋃ i, Z i,
        2 ^ m ≤ (Finset.univ.filter fun i => p ∈ Z i).card ∧
          (Finset.univ.filter fun i => p ∈ Z i).card < 2 ^ (m + 1) := by
  obtain ⟨m, A, hm, hA, hmass⟩ := common_cell_multiplicity_level μ V k
    (fun j p hp => (hlevel j p hp).1)
  let F' : Fin N → Finset X := fun j => if j ∈ A then F j else ∅
  let V' : Fin N → Fin n → Set X := fun j i => if j ∈ A then V j i else ∅
  have hFF (j : Fin N) (z : X) (hz : z ∈ F' j) : j ∈ A ∧ z ∈ F j := by
    by_cases hj : j ∈ A
    · exact ⟨hj, by simpa only [F', if_pos hj] using hz⟩
    · simp only [F', if_neg hj, Finset.notMem_empty] at hz
  have hVsub (j : Fin N) (i : Fin n) : V' j i ⊆ V j i := by
    by_cases hj : j ∈ A <;> simp [V', hj]
  have hV' (j : Fin N) (i : Fin n) : MeasurableSet (V' j i) ∧ V' j i ⊆ Y i ∩ C j := by
    refine ⟨?_, (hVsub j i).trans (hV j i).2⟩
    by_cases hj : j ∈ A <;> simp [V', hj, (hV j i).1]
  have hHdisj' (j : Fin N) : (↑(F' j) : Set X).PairwiseDisjoint (H j) :=
    fun z hz w hw hzw => hHdisj j (hFF j z hz).2 (hFF j w hw).2 hzw
  have hHunion' (j : Fin N) : (⋃ z ∈ F' j, H j z) = ⋃ i, V' j i := by
    by_cases hj : j ∈ A
    · simpa only [F', V', if_pos hj] using hHunion j
    · simp [F', V', hj]
  have hlocal' : ∀ j z, z ∈ F' j → ∀ i, (V' j i ∩ H j z).Nonempty →
      V' j i ∩ P j z ⊆ H j z ∧ Q i j z := by
    intro j z hz i hi
    have hj := (hFF j z hz).1
    simpa only [V', if_pos hj] using hlocal j z (hFF j z hz).2 i
      (by simpa only [V', if_pos hj] using hi)
  have hdense' (j : Fin N) : b * (F' j).card ≤ ∑ z ∈ F' j, μ (H j z) := by
    by_cases hj : j ∈ A
    · simpa only [F', if_pos hj] using hdense j
    · simp only [F', if_neg hj, Finset.card_empty, Nat.cast_zero, mul_zero, Finset.sum_empty, le_refl]
  obtain ⟨L, cell, z, Z, hmem, hZeq, hZ, haccount, hdisj, hunion, _, hdensity, htrigger⟩ :=
    assemble_separated_cell_pieces μ hr Y C q F' V' H P Q hCdisj hV'
      (fun j i => (hVsub j i).trans (hVball j i))
      (fun i j l hjl hj hl => hsep i j l hjl (hj.mono (hVsub j i)) (hl.mono (hVsub l i)))
      hHdisj' hHunion' (fun j z hz => hP j z (hFF j z hz).2) hlocal'
      (a := 0) (by simp) hdense'
  have hselected : (∑ j, ∑ i, μ (V' j i)) = ∑ j ∈ A, ∑ i, μ (V j i) := by
    simp only [V', apply_ite, measure_empty, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_mem, Finset.univ_inter]
  refine ⟨m, L, cell, z, Z, hm, fun l => (hFF _ _ (hmem l)).2, hZ,
    hdisj, hunion, ?_, hdensity, htrigger, ?_⟩
  · calc
      _ ≤ ∑ j, ∑ i, μ (V j i) := hkeep
      _ ≤ (Nat.log 2 n + 1 : ℕ) * ∑ j ∈ A, ∑ i, μ (V j i) := hmass
      _ = _ := by rw [← hselected, ← haccount]
  · have hlevel' : ∀ j p, p ∈ ⋃ i, V' j i →
        2 ^ m ≤ (Finset.univ.filter fun i => p ∈ V' j i).card ∧
          (Finset.univ.filter fun i => p ∈ V' j i).card < 2 ^ (m + 1) := by
      intro j p hp
      by_cases hj : j ∈ A
      · have hp' : p ∈ ⋃ i, V j i := by simpa only [V', if_pos hj] using hp
        simpa only [V', if_pos hj, hA j hj] using hlevel j p hp'
      · simp only [V', if_neg hj, iUnion_empty, mem_empty_iff_false] at hp
    intro p hp
    have hp' : p ∈ ⋃ i, ⋃ j, V' j i := by simpa only [hZeq] using hp
    have hh := disjoint_cells_common_level C V' hCdisj
      (fun j i => (hV' j i).2.trans inter_subset_right) hlevel' p hp'
    simpa only [hZeq] using hh

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
