-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy.Cells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabExtraction

/-!
# Bookkeeping for the cells of a greedy extraction

For cells with pairwise disjoint supports, the shadings of a fixed index in different cells are
disjoint subsets of its original shading. Hence the total cell mass is controlled by the original
mass of the indices involved, and an index lies in at most `1/θ` cells.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells

local notation "Sp" => LeanEval.Analysis.WangZahlKakeya.Space

section
variable {n m : ℕ} {C : Fin m → ShadedCell (Fin n)} {F : Finset (Fin n)}
  {U Y : Fin n → Set Sp} {θ : ℝ≥0∞} {Good : Finset (Fin n) → Set Sp → Prop}

lemma shading_subset_support {D : ShadedCell (Fin n)} {i : Fin n} (hi : i ∈ D.indices) :
    D.shading i ⊆ D.support :=
  subset_biUnion_of_mem (u := D.shading) hi

/-- Sum over cells and their indices, regrouped by index. -/
lemma sum_cells_comm (J : Finset (Fin m)) (g : Fin m → Fin n → ℝ≥0∞) :
    ∑ j ∈ J, ∑ i ∈ (C j).indices, g j i =
      ∑ i ∈ J.biUnion (fun j => (C j).indices), ∑ j ∈ J.filter (fun j => i ∈ (C j).indices), g j i := by
  classical
  apply Finset.sum_comm'
  intro j i
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨hj, hi⟩; exact ⟨⟨hj, hi⟩, j, hj, hi⟩
  · rintro ⟨⟨hj, hi⟩, _⟩; exact ⟨hj, hi⟩

/-- For a fixed index, its shadings in distinct cells are disjoint subsets of `Y i`. -/
lemma sum_shadings_le (hC : ∀ j, (C j).Valid F U Y θ Good)
    (hdisj : Pairwise (fun j k => Disjoint (C j).support (C k).support))
    (J : Finset (Fin m)) (i : Fin n) :
    ∑ j ∈ J.filter (fun j => i ∈ (C j).indices), volume ((C j).shading i) ≤ volume (Y i) := by
  classical
  rw [← measure_biUnion_finset]
  · apply measure_mono
    intro p hp
    obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp hp
    exact (hC j).2.2.2.2.2.1 i (Finset.mem_filter.mp hj).2 hpj
  · intro j hj j' hj' hne
    exact (hdisj hne).mono (shading_subset_support (Finset.mem_filter.mp hj).2)
      (shading_subset_support (Finset.mem_filter.mp hj').2)
  · intro j hj
    exact (hC j).2.2.2.2.1 i (Finset.mem_filter.mp hj).2

/-- The total shading mass of a family of cells is at most the original mass of their indices. -/
lemma cells_shading_le (hC : ∀ j, (C j).Valid F U Y θ Good)
    (hdisj : Pairwise (fun j k => Disjoint (C j).support (C k).support)) (J : Finset (Fin m)) :
    ∑ j ∈ J, ∑ i ∈ (C j).indices, volume ((C j).shading i) ≤
      ∑ i ∈ J.biUnion (fun j => (C j).indices), volume (Y i) := by
  rw [sum_cells_comm]
  exact Finset.sum_le_sum (fun i _ => sum_shadings_le hC hdisj J i)

/-- The total container mass of a family of cells, times `θ`, is at most the original mass. -/
lemma cells_mass_le (hC : ∀ j, (C j).Valid F U Y θ Good)
    (hdisj : Pairwise (fun j k => Disjoint (C j).support (C k).support)) (J : Finset (Fin m)) :
    θ * ∑ j ∈ J, ∑ i ∈ (C j).indices, volume (U i) ≤
      ∑ i ∈ J.biUnion (fun j => (C j).indices), volume (Y i) := by
  refine le_trans ?_ (cells_shading_le hC hdisj J)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => (hC j).2.2.2.2.2.2 i hi)

/-- An index lies in at most `1/θ` cells. -/
lemma card_cells_containing_le (hC : ∀ j, (C j).Valid F U Y θ Good)
    (hdisj : Pairwise (fun j k => Disjoint (C j).support (C k).support))
    (hYU : ∀ i ∈ F, Y i ⊆ U i) (i : Fin n) (hU0 : volume (U i) ≠ 0) (hUt : volume (U i) ≠ ⊤)
    (J : Finset (Fin m)) :
    θ * ((J.filter (fun j => i ∈ (C j).indices)).card : ℝ≥0∞) ≤ 1 := by
  classical
  set A := J.filter (fun j => i ∈ (C j).indices) with hAdef
  rcases A.eq_empty_or_nonempty with hA | ⟨j₀, hj₀⟩
  · rw [hA]; simp
  have hiF : i ∈ F := (hC j₀).2.1 (Finset.mem_filter.mp hj₀).2
  have h1 : θ * (A.card : ℝ≥0∞) * volume (U i) ≤ 1 * volume (U i) := by
    calc θ * (A.card : ℝ≥0∞) * volume (U i)
        = ∑ j ∈ A, θ * volume (U i) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ j ∈ A, volume ((C j).shading i) :=
          Finset.sum_le_sum (fun j hj => (hC j).2.2.2.2.2.2 i (Finset.mem_filter.mp hj).2)
      _ ≤ volume (Y i) := sum_shadings_le hC hdisj J i
      _ ≤ volume (U i) := measure_mono (hYU i hiF)
      _ = 1 * volume (U i) := (one_mul _).symm
  exact (ENNReal.mul_le_mul_iff_left hU0 hUt).mp h1

/-- The number of (cell, index) incidences is at most `1/θ` times the number of indices. -/
lemma cells_card_le (hC : ∀ j, (C j).Valid F U Y θ Good)
    (hdisj : Pairwise (fun j k => Disjoint (C j).support (C k).support))
    (hYU : ∀ i ∈ F, Y i ⊆ U i) (hU0 : ∀ i, volume (U i) ≠ 0) (hUt : ∀ i, volume (U i) ≠ ⊤)
    (J : Finset (Fin m)) :
    θ * ∑ j ∈ J, ((C j).indices.card : ℝ≥0∞) ≤
      ((J.biUnion (fun j => (C j).indices)).card : ℝ≥0∞) := by
  classical
  have h : ∑ j ∈ J, ((C j).indices.card : ℝ≥0∞) =
      ∑ j ∈ J, ∑ i ∈ (C j).indices, (1 : ℝ≥0∞) := by simp
  rw [h, sum_cells_comm (C := C) J (fun _ _ => (1 : ℝ≥0∞)), Finset.mul_sum]
  calc ∑ i ∈ J.biUnion (fun j => (C j).indices),
        θ * ∑ j ∈ J.filter (fun j => i ∈ (C j).indices), (1 : ℝ≥0∞)
      ≤ ∑ i ∈ J.biUnion (fun j => (C j).indices), (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro i _
        simpa using card_cells_containing_le hC hdisj hYU i (hU0 i) (hUt i) J
    _ = ((J.biUnion (fun j => (C j).indices)).card : ℝ≥0∞) := by simp

end

end WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy
