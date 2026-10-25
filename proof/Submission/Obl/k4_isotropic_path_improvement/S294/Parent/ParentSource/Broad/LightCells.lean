-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.LightCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/LightCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/LightCells.lean.
All earlier source attributions below are retained. -/
import Mathlib

/-!
# Pruning light cells

Given finitely many disjoint measurable cells, keep only the cells of mass at least `mcell`.
The removed mass is less than `mcell` times the number of light cells, and on the kept part
every cell has mass either zero or at least `mcell`.  This is the "no light observation
cells" preparation (S4) of the broad completion, once the occupied observation cells are
counted.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}

open Classical in
/-- The union of the heavy cells. -/
def heavyCells (μ : Measure Ω) (S : Finset ι) (C : ι → Set Ω) (mcell : ℝ≥0∞) : Set Ω :=
  ⋃ k ∈ S.filter (fun k => mcell ≤ μ (C k)), C k

open Classical in
/-- **Pruning loss.**  The cells of `S` outside the heavy cells carry less than `mcell` each. -/
theorem measure_diff_heavyCells_le (μ : Measure Ω) (S : Finset ι) (C : ι → Set Ω)
    (mcell : ℝ≥0∞) (X : Set Ω) (hX : X ⊆ ⋃ k ∈ S, C k) :
    μ (X \ heavyCells μ S C mcell) ≤ ((S.filter (fun k => μ (C k) < mcell)).card : ℝ≥0∞) *
      mcell := by
  have hsub : X \ heavyCells μ S C mcell ⊆ ⋃ k ∈ S.filter (fun k => μ (C k) < mcell), C k := by
    intro q ⟨hqX, hqH⟩
    obtain ⟨k, hkS, hqk⟩ := Set.mem_iUnion₂.mp (hX hqX)
    refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨hkS, ?_⟩, hqk⟩
    by_contra hk
    push Not at hk
    exact hqH (Set.mem_iUnion₂.mpr ⟨k, Finset.mem_filter.mpr ⟨hkS, hk⟩, hqk⟩)
  calc μ (X \ heavyCells μ S C mcell)
      ≤ μ (⋃ k ∈ S.filter (fun k => μ (C k) < mcell), C k) := measure_mono hsub
    _ ≤ ∑ k ∈ S.filter (fun k => μ (C k) < mcell), μ (C k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ S.filter (fun k => μ (C k) < mcell), mcell :=
        Finset.sum_le_sum (fun k hk => (Finset.mem_filter.mp hk).2.le)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

open Classical in
/-- **No light cells after pruning.**  For disjoint cells, the restriction to the heavy cells
gives every cell of `S` mass zero or at least `mcell`. -/
theorem restrict_heavyCells_cell (μ : Measure Ω) (S : Finset ι) (C : ι → Set Ω)
    (mcell : ℝ≥0∞) (hdisj : (S : Set ι).PairwiseDisjoint C)
    (hCm : ∀ k ∈ S, MeasurableSet (C k)) (k : ι) (hk : k ∈ S) :
    (μ.restrict (heavyCells μ S C mcell)) (C k) = 0 ∨
      mcell ≤ (μ.restrict (heavyCells μ S C mcell)) (C k) := by
  rw [Measure.restrict_apply (hCm k hk)]
  by_cases hheavy : mcell ≤ μ (C k)
  · right
    have : C k ∩ heavyCells μ S C mcell = C k := by
      apply Set.inter_eq_left.mpr
      exact Set.subset_iUnion₂_of_subset k (Finset.mem_filter.mpr ⟨hk, hheavy⟩) le_rfl
    rw [this]; exact hheavy
  · left
    have : C k ∩ heavyCells μ S C mcell = ∅ := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hqk hqH
      obtain ⟨k', hk', hqk'⟩ := Set.mem_iUnion₂.mp hqH
      obtain ⟨hk'S, hk'heavy⟩ := Finset.mem_filter.mp hk'
      by_cases hkk : k = k'
      · subst hkk; exact hheavy hk'heavy
      · exact Set.disjoint_left.mp (hdisj hk hk'S hkk) hqk hqk'
    rw [this, measure_empty]

section Fibres

/-! ### Cells as the fibres of an index map -/

variable {κ : Type*} [MeasurableSpace κ] [MeasurableSingletonClass κ] [Countable κ]

/-- The incidences whose cell (fibre of `idx`) has mass at least `mcell`. -/
def heavySet (μ : Measure Ω) (idx : Ω → κ) (mcell : ℝ≥0∞) : Set Ω :=
  idx ⁻¹' {k | mcell ≤ μ (idx ⁻¹' {k})}

lemma measurableSet_heavySet (μ : Measure Ω) {idx : Ω → κ} (hidx : Measurable idx)
    (mcell : ℝ≥0∞) : MeasurableSet (heavySet μ idx mcell) :=
  hidx (Set.to_countable _).measurableSet

omit [Countable κ] in
/-- **No light cells after pruning.** -/
theorem restrict_heavySet_fibre (μ : Measure Ω) {idx : Ω → κ} (hidx : Measurable idx)
    (mcell : ℝ≥0∞) (k : κ) :
    (μ.restrict (heavySet μ idx mcell)) (idx ⁻¹' {k}) = 0 ∨
      mcell ≤ (μ.restrict (heavySet μ idx mcell)) (idx ⁻¹' {k}) := by
  rw [Measure.restrict_apply (hidx (measurableSet_singleton k))]
  by_cases hk : mcell ≤ μ (idx ⁻¹' {k})
  · right
    have : idx ⁻¹' {k} ∩ heavySet μ idx mcell = idx ⁻¹' {k} := by
      apply Set.inter_eq_left.mpr
      intro q hq
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq
      show mcell ≤ μ (idx ⁻¹' {idx q})
      rw [hq]; exact hk
    rw [this]; exact hk
  · left
    have : idx ⁻¹' {k} ∩ heavySet μ idx mcell = ∅ := by
      ext q
      simp only [heavySet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hq h
      rw [hq] at h
      exact hk h
    rw [this, measure_empty]

omit [MeasurableSpace κ] [MeasurableSingletonClass κ] [Countable κ] in
open Classical in
/-- **Pruning loss.**  If `μ` is carried by the cells of a finite index set `S`, deleting the
light cells costs at most `#S · mcell`. -/
theorem measure_compl_heavySet_le (μ : Measure Ω) (idx : Ω → κ) (mcell : ℝ≥0∞)
    (S : Finset κ) (hS : μ {q | idx q ∉ S} = 0) :
    μ (heavySet μ idx mcell)ᶜ ≤ (S.card : ℝ≥0∞) * mcell := by
  set S' := S.filter (fun k => μ (idx ⁻¹' {k}) < mcell) with hS'
  have hsub : (heavySet μ idx mcell)ᶜ ⊆ {q | idx q ∉ S} ∪ ⋃ k ∈ S', idx ⁻¹' {k} := by
    intro q hq
    by_cases hqS : idx q ∈ S
    · right
      refine Set.mem_iUnion₂.mpr ⟨idx q, Finset.mem_filter.mpr ⟨hqS, ?_⟩, rfl⟩
      simp only [heavySet, Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_le] at hq
      exact hq
    · left; exact hqS
  calc μ (heavySet μ idx mcell)ᶜ
      ≤ μ ({q | idx q ∉ S} ∪ ⋃ k ∈ S', idx ⁻¹' {k}) := measure_mono hsub
    _ ≤ μ {q | idx q ∉ S} + μ (⋃ k ∈ S', idx ⁻¹' {k}) := measure_union_le _ _
    _ ≤ 0 + ∑ k ∈ S', μ (idx ⁻¹' {k}) := by
        rw [hS]; gcongr; exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ S', mcell := by
        rw [zero_add]
        exact Finset.sum_le_sum (fun k hk => (Finset.mem_filter.mp hk).2.le)
    _ = (S'.card : ℝ≥0∞) * mcell := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S.card : ℝ≥0∞) * mcell := by
        gcongr
        exact Finset.filter_subset _ S

end Fibres

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad
