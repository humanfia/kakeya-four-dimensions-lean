-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.MappedCellAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.UniformCellAssembly

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set Metric
open scoped Classical

set_option maxHeartbeats 1000000 in
/-- Assemble packets separated after a common change of coordinates.
The measure, pieces, and shadings remain in the original coordinates. -/
theorem assemble_uniform_cell_pieces_mapped {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (φ : X → X) {r : ℝ} (hr : 0 < r) {n N : ℕ}
    (Y : Fin n → Set X) (C : Fin N → Set X) (q : Fin N → X)
    (F : Fin N → Finset X) (V : Fin N → Fin n → Set X)
    (H P : Fin N → X → Set X) (Q : Fin n → Fin N → X → Prop) (k : Fin N → ℕ)
    (hCdisj : Pairwise fun j l => Disjoint (C j) (C l))
    (hV : ∀ j i, MeasurableSet (V j i) ∧ V j i ⊆ Y i ∩ C j)
    (hVball : ∀ j i, V j i ⊆ φ ⁻¹' ball (φ (q j)) r)
    (hsep : ∀ i j l, j ≠ l → (V j i).Nonempty → (V l i).Nonempty →
      10 * r < dist (φ (q j)) (φ (q l)))
    (hHdisj : ∀ j, (↑(F j) : Set X).PairwiseDisjoint (H j))
    (hHunion : ∀ j, (⋃ z ∈ F j, H j z) = ⋃ i, V j i)
    (hP : ∀ j z, z ∈ F j → P j z ⊆ φ ⁻¹' ball (φ (q j)) (3 * r))
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
  letI : PseudoMetricSpace X := PseudoMetricSpace.induced φ inferInstance
  exact assemble_uniform_cell_pieces μ hr Y C q F V H P Q k hCdisj hV hVball hsep
    hHdisj hHunion hP hlocal hlevel hkeep hdense

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
