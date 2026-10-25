-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.SparseCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.SeparatedCubes

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open scoped Classical

/-- Sparse cells are charged only to the tubes meeting them. This preserves
all incidences in every retained cell, so both broadness and a common
multiplicity level survive unchanged. -/
theorem discard_sparse_cells {n : ℕ} {ι : Type*} [DecidableEq ι]
    (G : Finset ι) (C : ι → Set Space) (Y : Fin n → Set Space)
    (hcover : ∀ i, Y i ⊆ ⋃ j ∈ G, C j)
    {D v B : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v)
    (hbudget : (∑ i, (((G.filter fun j => (Y i ∩ C j).Nonempty).card : ℝ) * v)) ≤ B) :
    ∃ F : Finset ι, F ⊆ G ∧
      (∀ j ∈ F, ENNReal.ofReal (D * v) ≤ volume ((⋃ i, Y i) ∩ C j)) ∧
      (∑ i, volume (Y i)) ≤ (∑ i, volume (Y i ∩ ⋃ j ∈ F, C j)) +
        ENNReal.ofReal (D * B) := by
  classical
  let F := G.filter fun j => ENNReal.ofReal (D * v) ≤ volume ((⋃ i, Y i) ∩ C j)
  let R : Set Space := ⋃ j ∈ F, C j
  have hF : F ⊆ G := Finset.filter_subset _ _
  have hcost (i : Fin n) : volume (Y i \ R) ≤
      ENNReal.ofReal (D * ((G.filter fun j => (Y i ∩ C j).Nonempty).card : ℝ) * v) := by
    have hsub : Y i \ R ⊆ ⋃ j ∈ G, (Y i ∩ C j) \ R := by
      intro p hp
      obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.mp (hcover i hp.1)
      exact Set.mem_iUnion₂.mpr ⟨j, hj, ⟨hp.1, hpj⟩, hp.2⟩
    calc
      _ ≤ volume (⋃ j ∈ G, (Y i ∩ C j) \ R) := measure_mono hsub
      _ ≤ ∑ j ∈ G, volume ((Y i ∩ C j) \ R) := measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ G, if (Y i ∩ C j).Nonempty then ENNReal.ofReal (D * v) else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hne : (Y i ∩ C j).Nonempty
        · rw [if_pos hne]
          by_cases hgood : j ∈ F
          · have hC : C j ⊆ R := Set.subset_iUnion₂_of_subset j hgood subset_rfl
            have he : (Y i ∩ C j) \ R = ∅ := sdiff_eq_empty.mpr (inter_subset_right.trans hC)
            rw [he, measure_empty]
            exact zero_le
          · have hbad : ¬ ENNReal.ofReal (D * v) ≤ volume ((⋃ i, Y i) ∩ C j) := by
              intro h
              exact hgood (Finset.mem_filter.mpr ⟨hj, h⟩)
            exact (measure_mono (sdiff_subset.trans
              (inter_subset_inter_left _ (Set.subset_iUnion Y i)))).trans (le_of_lt (lt_of_not_ge hbad))
        · rw [if_neg hne, Set.not_nonempty_iff_eq_empty.mp hne, empty_sdiff, measure_empty]
      _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring
  refine ⟨F, hF, fun j hj => (Finset.mem_filter.mp hj).2, ?_⟩
  calc
    _ ≤ ∑ i, (volume (Y i ∩ R) + volume (Y i \ R)) := by
      apply Finset.sum_le_sum
      intro i _
      have he : Y i = (Y i ∩ R) ∪ (Y i \ R) := by ext p; simp
      nth_rw 1 [he]
      exact measure_union_le _ _
    _ = (∑ i, volume (Y i ∩ R)) + ∑ i, volume (Y i \ R) := Finset.sum_add_distrib
    _ ≤ (∑ i, volume (Y i ∩ R)) + ∑ i,
        ENNReal.ofReal (D * ((G.filter fun j => (Y i ∩ C j).Nonempty).card : ℝ) * v) :=
      add_le_add le_rfl (Finset.sum_le_sum fun i _ => hcost i)
    _ ≤ _ := by
      refine add_le_add le_rfl ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hbudget hD
      simpa only [Finset.mul_sum, mul_assoc] using hh

end WangZahlLot.Obl.wz_broad_grains_initialization
