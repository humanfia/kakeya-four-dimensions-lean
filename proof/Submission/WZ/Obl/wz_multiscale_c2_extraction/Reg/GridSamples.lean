-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.GridSamples.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.HeightGrid

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

def gridHeightSamples (D : Set ℝ) (h H a : ℝ) (j : ℤ) : Set ℝ :=
  (D ∩ Icc ((j : ℝ) * h + 2 * a) (((j : ℝ) + 1) * h - 2 * a)) ∩
    safeGridHeights H (2 * h)

theorem isCompact_gridHeightSamples {D : Set ℝ} (hD : IsCompact D)
    (h H a : ℝ) (j : ℤ) : IsCompact (gridHeightSamples D h H a j) :=
  (hD.inter_right isClosed_Icc).inter_right (isClosed_safeGridHeights H (2 * h))

theorem gridHeightSamples_subset {D : Set ℝ} {h H a : ℝ} {j : ℤ} :
    gridHeightSamples D h H a j ⊆ D := fun _ hz => hz.1.1

/-- Trimming the fine-cell boundaries and avoiding coarse boundaries removes
only a union of narrow bands. -/
theorem gridHeightSamples_mass_error {μ : Measure ℝ} {L : ℝ≥0∞}
    (hμ : ∀ l u : ℝ, μ (Icc l u) ≤ L * ENNReal.ofReal (u - l))
    {D : Set ℝ} (hDbox : D ⊆ Icc (-1 : ℝ) 1)
    {h H a : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hH : 0 < H) (ha : 0 ≤ a) :
    μ (D \ ⋃ j : ↥(heightGrid h), gridHeightSamples D h H a j.1) ≤
      ((heightGrid h).card : ℝ≥0∞) * L * ENNReal.ofReal (4 * a) +
        ((heightGrid H).card : ℝ≥0∞) * L * ENNReal.ofReal (4 * h) := by
  have hsub : (D \ ⋃ j : ↥(heightGrid h), gridHeightSamples D h H a j.1) ⊆
      heightGridBand h (2 * a) ∪ heightGridBand H (2 * h) := by
    intro z hz
    have hzbox := hDbox hz.1
    by_cases hs : z ∈ safeGridHeights H (2 * h)
    · left
      let j := ⌊z / h⌋
      have hjmem := height_floor_mem hh hh1 hzbox
      have hjbounds := height_floor_bounds (z := z) hh
      have hout : z ∉ Icc ((j : ℝ) * h + 2 * a) (((j : ℝ) + 1) * h - 2 * a) := by
        intro hzin
        exact hz.2 (mem_iUnion.mpr ⟨⟨j, hjmem.1⟩, ⟨hz.1, hzin⟩, hs⟩)
      simp only [mem_Icc, not_and_or, not_le] at hout
      rcases hout with hlo | hhi
      · apply mem_iUnion.mpr
        refine ⟨⟨j, hjmem.1⟩, ?_⟩
        constructor <;> dsimp [j] at * <;> linarith [hjbounds.1]
      · apply mem_iUnion.mpr
        refine ⟨⟨j + 1, hjmem.2⟩, ?_⟩
        simp only [Int.cast_add, Int.cast_one]
        constructor <;> dsimp [j] at * <;> linarith [hjbounds.2]
    · exact Or.inr (outside_height_mem_band hH (by linarith) hzbox hs)
  calc
    μ (D \ ⋃ j : ↥(heightGrid h), gridHeightSamples D h H a j.1)
        ≤ μ (heightGridBand h (2 * a) ∪ heightGridBand H (2 * h)) := measure_mono hsub
    _ ≤ μ (heightGridBand h (2 * a)) + μ (heightGridBand H (2 * h)) := measure_union_le _ _
    _ ≤ ((heightGrid h).card : ℝ≥0∞) * L * ENNReal.ofReal (4 * a) +
        ((heightGrid H).card : ℝ≥0∞) * L * ENNReal.ofReal (4 * h) := by
      convert add_le_add (heightGridBand_mass hμ h (2 * a))
        (heightGridBand_mass hμ H (2 * h)) using 1 <;> congr 3 <;> ring

/-- Hulls of compact samples in trimmed distinct grid cells remain disjoint
after padding, without discarding an entire residue class of cells. -/
theorem padded_grid_sample_hulls_disjoint {D : Set ℝ} (hD : IsCompact D)
    {h H a : ℝ} (hh : 0 < h) (ha : 0 < a) {i j : ℤ} (hij : i ≠ j)
    (hi : (gridHeightSamples D h H a i).Nonempty)
    (hj : (gridHeightSamples D h H a j).Nonempty) :
    Disjoint
      (Icc (sInf (gridHeightSamples D h H a i) - a) (sSup (gridHeightSamples D h H a i) + a))
      (Icc (sInf (gridHeightSamples D h H a j) - a) (sSup (gridHeightSamples D h H a j) + a)) := by
  have hil := ((isCompact_gridHeightSamples hD h H a i).sInf_mem hi).1.2.1
  have hiu := ((isCompact_gridHeightSamples hD h H a i).sSup_mem hi).1.2.2
  have hjl := ((isCompact_gridHeightSamples hD h H a j).sInf_mem hj).1.2.1
  have hju := ((isCompact_gridHeightSamples hD h H a j).sSup_mem hj).1.2.2
  apply disjoint_left.mpr
  intro z hzi hzj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    nlinarith [hzi.2, hzj.1]
  · have hle : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hgt)
    nlinarith [hzj.2, hzi.1]

theorem grid_sample_hull_in_cells {D : Set ℝ} (hD : IsCompact D)
    {h H a : ℝ} (hh : 0 < h) (hH : 0 < H) (ha : 0 ≤ a) {j : ℤ}
    (hne : (gridHeightSamples D h H a j).Nonempty) :
    ∃ m : ℤ, Icc (sInf (gridHeightSamples D h H a j)) (sSup (gridHeightSamples D h H a j)) ⊆
      Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h) ∩ Icc ((m : ℝ) * H) (((m : ℝ) + 1) * H) := by
  obtain ⟨z, hz⟩ := hne
  have hzfine : z ∈ Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h) :=
    ⟨by linarith [hz.1.2.1], by linarith [hz.1.2.2]⟩
  obtain ⟨m, hm⟩ := grid_cell_contained_of_safe hh hH hzfine hz.2
  have hl := ((isCompact_gridHeightSamples hD h H a j).sInf_mem ⟨z, hz⟩).1.2.1
  have hu := ((isCompact_gridHeightSamples hD h H a j).sSup_mem ⟨z, hz⟩).1.2.2
  refine ⟨m, ?_⟩
  intro t ht
  have htfine : t ∈ Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨htfine, hm htfine⟩

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
