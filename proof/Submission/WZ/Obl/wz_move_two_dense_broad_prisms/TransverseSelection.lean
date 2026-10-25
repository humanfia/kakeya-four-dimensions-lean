-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.TransverseSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.AxialGeometry
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Geometry
import Submission.WZ.Obl.wz_c2_slope_normalization.BoundedSlope

/-! Selecting one transverse coordinate for the Córdoba argument. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory
open scoped ENNReal

/-- Projectively transverse partners have a large component in one of the two
transverse coordinates. Selecting one coordinate costs at most half the stem mass. -/
theorem select_transverse_coordinate {n : ℕ} {r : ℝ} {u : V} (hu : ‖u‖ = 1)
    (hr : 0 ≤ r) (v : Fin n → V) (hv : ∀ i, ‖v i‖ = 1)
    (Y : Fin n → Set V) (hYm : ∀ i, MeasurableSet (Y i))
    (E : Set V) (hEm : MeasurableSet E) (hEfin : volume E ≠ ∞)
    (hpartner : ∀ p ∈ E, ∃ i, p ∈ Y i ∧ r < min ‖v i-u‖ ‖v i+u‖) :
    ∃ (g : V ≃ₗᵢ[ℝ] V) (E' : Set V),
      (∀ p, g p 2 = inner ℝ u p) ∧ MeasurableSet E' ∧ E' ⊆ E ∧
      volume.real E / 2 ≤ volume.real E' ∧
      ∀ p ∈ E', ∃ i, p ∈ Y i ∧ r/4 ≤ |g (v i) 1| := by
  classical
  obtain ⟨g, hg⟩ := wz_broad_grains_initialization.frame_last_of_unit hu
  have hg2 : ∀ p, g p 2 = inner ℝ u p := frame_last_inner hg
  let U : Fin 3 → Set V := fun j => E ∩ ⋃ i : Fin n,
    if r/4 ≤ |g (v i) j| then Y i else ∅
  have hUm : ∀ j, MeasurableSet (U j) := by
    intro j
    apply hEm.inter
    apply MeasurableSet.iUnion
    intro i
    split_ifs <;> simp_all only [MeasurableSet.empty]
  have hUE : ∀ j, U j ⊆ E := fun _ => inter_subset_left
  have hUfin : ∀ j, volume (U j) ≠ ∞ := fun j => measure_ne_top_of_subset (hUE j) hEfin
  have hmem (j : Fin 3) (p : V) : p ∈ U j ↔ p ∈ E ∧ ∃ i, p ∈ Y i ∧ r/4 ≤ |g (v i) j| := by
    simp only [U, mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨hpE, i, hi⟩
      split_ifs at hi with hdir
      · exact ⟨hpE, i, hi, hdir⟩
      · exact hi.elim
    · rintro ⟨hpE, i, hi, hdir⟩
      exact ⟨hpE, i, by simpa only [if_pos hdir] using hi⟩
  have hcover : E ⊆ U 0 ∪ U 1 := by
    intro p hpE
    obtain ⟨i, hi, hang⟩ := hpartner p hpE
    by_cases h0 : r/4 ≤ |g (v i) 0|
    · exact Or.inl ((hmem 0 p).mpr ⟨hpE, i, hi, h0⟩)
    · have h1 := wz_flat_cluster_slab_filling.inplane_large hu (hv i) hg2 hr hang
        (le_of_not_ge h0)
      exact Or.inr ((hmem 1 p).mpr ⟨hpE, i, hi, by linarith⟩)
  have hmass : volume.real E ≤ volume.real (U 0) + volume.real (U 1) := by
    exact (measureReal_mono hcover (measure_union_lt_top (hUfin 0).lt_top (hUfin 1).lt_top).ne).trans
      (measureReal_union_le _ _)
  by_cases h1 : volume.real E / 2 ≤ volume.real (U 1)
  · refine ⟨g, U 1, hg2, hUm 1, hUE 1, h1, ?_⟩
    intro p hp
    exact ((hmem 1 p).mp hp).2
  · let g' := g.trans wz_c2_slope_normalization.swapXY
    have hg'2 : ∀ p, g' p 2 = inner ℝ u p := by
      intro p
      exact hg2 p
    refine ⟨g', U 0, hg'2, hUm 0, hUE 0, by linarith, ?_⟩
    intro p hp
    obtain ⟨i, hi, hdir⟩ := ((hmem 0 p).mp hp).2
    refine ⟨i, hi, ?_⟩
    simpa only [g', LinearIsometryEquiv.trans_apply, wz_c2_slope_normalization.swapXY_one] using hdir

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
