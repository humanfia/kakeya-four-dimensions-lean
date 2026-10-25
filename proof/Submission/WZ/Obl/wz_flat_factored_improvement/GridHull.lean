-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.GridHull.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.ShortMap

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement
  (gridCell gridUnion gridCell_dist_lt gridUnion_measurable gridUnion_volume_ne_top
    tube_gridUnion_volumeReal)

noncomputable def gridHull (a : ℝ) (s : Finset (Fin 3 → ℤ)) (Y : Set Space) : Set Space := by
  classical
  exact gridUnion a (s.filter (fun z => (Y ∩ gridCell a z).Nonempty))

theorem gridHull_measurable (a : ℝ) (s : Finset (Fin 3 → ℤ)) (Y : Set Space) :
    MeasurableSet (gridHull a s Y) := gridUnion_measurable _ _

theorem gridHull_volume_ne_top {a : ℝ} (ha : 0 < a) (s : Finset (Fin 3 → ℤ)) (Y : Set Space) :
    volume (gridHull a s Y) ≠ ⊤ := gridUnion_volume_ne_top ha _

theorem subset_gridHull {a : ℝ} {s : Finset (Fin 3 → ℤ)} {Y : Set Space}
    (hY : Y ⊆ gridUnion a s) : Y ⊆ gridHull a s Y := by
  classical
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp (hY hp)
  exact mem_iUnion₂.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, ⟨p, hp, hpz⟩⟩, hpz⟩

theorem gridHull_subset (a : ℝ) (s : Finset (Fin 3 → ℤ)) (Y : Set Space) :
    gridHull a s Y ⊆ gridUnion a s := by
  classical
  rintro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
  exact mem_iUnion₂.mpr ⟨z, (Finset.mem_filter.mp hz).1, hpz⟩

theorem gridHull_subset_thickTube {δ a : ℝ} (ha : 0 < a) (hδa : δ ≤ a)
    (s : Finset (Fin 3 → ℤ)) {x v : Space} {Y : Set Space}
    (hYT : Y ⊆ Tube δ x v) : gridHull a s Y ⊆ Tube (3 * a) x v := by
  classical
  intro p hp
  obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
  obtain ⟨q, hq, hqz⟩ := (Finset.mem_filter.mp hz).2
  obtain ⟨w, hw, hqw⟩ := mem_thickening_iff.mp (hYT hq)
  refine mem_thickening_iff.mpr ⟨w, hw, ?_⟩
  have hpq := gridCell_dist_lt ha hpz hqz
  have hh := dist_triangle p q w
  linarith

theorem gridHull_density {δ a lam : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hlam : 0 ≤ lam)
    (s : Finset (Fin 3 → ℤ)) {x v : Space} (hv : ‖v‖ = 1) {Y : Set Space}
    (hYT : Y ⊆ Tube δ x v) (hYgrid : Y ⊆ gridUnion a s)
    (hden : ENNReal.ofReal (lam * δ ^ 2) ≤ volume Y) :
    ENNReal.ofReal (lam * a ^ 2 / 16) ≤ volume (gridHull a s Y) := by
  have hsub : Y ⊆ Tube δ x v ∩ gridHull a s Y := subset_inter hYT (subset_gridHull hYgrid)
  have hfin := gridHull_volume_ne_top ha s Y
  have hh := (ENNReal.ofReal_le_iff_le_toReal
    (ne_top_of_le_ne_top hfin (measure_mono (hsub.trans inter_subset_right)))).mp hden
  have hvol : volume.real Y ≤ 16 * δ ^ 2 / a ^ 2 * volume.real (gridHull a s Y) := by
    exact (measureReal_mono hsub
      (ne_top_of_le_ne_top hfin (measure_mono inter_subset_right))).trans
        (tube_gridUnion_volumeReal ha δ x v hv _)
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 16 * δ ^ 2 / a ^ 2)).mp
  have he : (16 * δ ^ 2 / a ^ 2) * (lam * a ^ 2 / 16) = lam * δ ^ 2 := by field_simp
  rw [he]
  exact hh.trans hvol

end WangZahlLot.Obl.wz_flat_factored_improvement
