-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.LightRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.LightClass
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.CompactRefinement

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- Removing the preimage of a planar set commutes with the projected union. -/
lemma projection_iUnion_sdiff_preimage {n : ℕ} (f : ℝ → ℝ) (Y : Fin n → Set Space)
    (L : Set (ℝ × ℝ)) :
    projection f '' (⋃ i, Y i \ projection f ⁻¹' L) =
      (projection f '' (⋃ i, Y i)) \ L := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact ⟨mem_image_of_mem _ (mem_iUnion.mpr ⟨i, hi.1⟩), hi.2⟩
  · rintro ⟨⟨q, hq, rfl⟩, hqL⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact ⟨q, mem_iUnion.mpr ⟨i, hi, hqL⟩, rfl⟩

/-- Once light projected cells carry at most half the mass, their complement supplies
an actual measurable shading refinement and the desired area comparison. -/
theorem refinement_of_light_mass {n : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i))
    (hfinite : (∑ i, volume (Y i)) ≠ ⊤) {ρ : ℝ} {α : ℝ≥0∞}
    (L : Set (ℝ × ℝ)) (hL : MeasurableSet L)
    (hmass : (∑ i, volume (Y i ∩ projection f ⁻¹' L)) ≤ (∑ i, volume (Y i)) / 2)
    (harea : (9 * α) * volume (thickening ρ ((projection f '' (⋃ i, Y i)) \ L)) ≤
      9 * volume ((projection f '' (⋃ i, Y i)) \ L)) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧
      (∑ i, volume (Y i)) / 2 ≤ ∑ i, volume (Z i) ∧
      α * volume (thickening ρ (projection f '' (⋃ i, Z i))) ≤
        volume (projection f '' (⋃ i, Z i)) := by
  let Z : Fin n → Set Space := fun i => Y i \ projection f ⁻¹' L
  have hpre : MeasurableSet (projection f ⁻¹' L) := (continuous_projection hf).measurable hL
  have he : (∑ i, volume (Y i ∩ projection f ⁻¹' L)) + ∑ i, volume (Z i) =
      ∑ i, volume (Y i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => measure_inter_add_sdiff (Y i) hpre
  refine ⟨Z, fun i => (hY i).diff hpre, fun i => sdiff_subset, ?_, ?_⟩
  · apply ENNReal.le_of_add_le_add_left
      (show (∑ i, volume (Y i)) / 2 ≠ ⊤ from ENNReal.div_ne_top hfinite (by norm_num))
    calc
      (∑ i, volume (Y i)) / 2 + (∑ i, volume (Y i)) / 2 = ∑ i, volume (Y i) :=
        ENNReal.add_halves _
      _ = (∑ i, volume (Y i ∩ projection f ⁻¹' L)) + ∑ i, volume (Z i) := he.symm
      _ ≤ (∑ i, volume (Y i)) / 2 + ∑ i, volume (Z i) := add_le_add hmass le_rfl
  · dsimp only [Z]
    rw [projection_iUnion_sdiff_preimage]
    apply (ENNReal.mul_le_mul_iff_right (by norm_num : (9 : ℝ≥0∞) ≠ 0)
      (by norm_num : (9 : ℝ≥0∞) ≠ ⊤)).mp
    simpa only [mul_assoc] using harea

/-- A sufficient condition for the coarse/fine conclusion at a prescribed scale:
only the light-cell mass estimate remains to be supplied. -/
theorem exists_refinement_of_grid_light_mass {n : ℕ} {f : ℝ → ℝ} (hf : Continuous f)
    (Y : Fin n → Set Space) (hY : ∀ i, MeasurableSet (Y i))
    (hfinite : (∑ i, volume (Y i)) ≠ ⊤) {ρ : ℝ} (hρ : 0 < ρ) (α : ℝ≥0∞)
    (hremove : ∀ L : Set (ℝ × ℝ), MeasurableSet L →
      (∀ S : Set (ℝ × ℝ), volume ((projection f '' (⋃ i, Y i)) ∩ L ∩ S) ≤
        (9 * α) * volume (thickening ρ S)) →
      (∑ i, volume (Y i ∩ projection f ⁻¹' L)) ≤ (∑ i, volume (Y i)) / 2) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ Y i) ∧
      (∑ i, volume (Y i)) / 2 ≤ ∑ i, volume (Z i) ∧
      α * volume (thickening ρ (projection f '' (⋃ i, Z i))) ≤
        volume (projection f '' (⋃ i, Z i)) := by
  obtain ⟨L, hL, hlight, hdense⟩ := planar_grid_density_split
    (projection f '' (⋃ i, Y i)) hρ (9 * α)
  exact refinement_of_light_mass hf Y hY hfinite L hL (hremove L hL hlight) hdense

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
